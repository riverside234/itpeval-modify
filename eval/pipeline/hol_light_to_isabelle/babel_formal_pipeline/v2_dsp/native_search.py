"""Full-session native jobs, strict XML protocol and independent proof replay."""
from __future__ import annotations

import json
import re
import shutil
import time
import uuid
import xml.etree.ElementTree as ET
from pathlib import Path

from ..common import fingerprint, repo_path
from ..isabelle_syntax import inventory_isabelle_declarations, tokens
from ..theory_context import normalize_body, validate_context
from .runtime import DspConfig, NATIVE_DIR, RUNTIME_DIR, OwnedProcess, adapter_hashes

PROTOCOL_VERSION = "dsp_native_request_v1"
RESULT_VERSION = "dsp_native_result_v1"


class NativeFailure(RuntimeError):
    def __init__(self, category: str, message: str):
        super().__init__(message)
        self.category = category


def imports_of(prefix: str) -> list[str]:
    items = tokens(prefix)
    start = next((i + 1 for i, t in enumerate(items) if t.kind == "word" and t.text == "imports"), None)
    if start is None:
        raise ValueError("missing original theory imports")
    end = next((i for i in range(start, len(items)) if items[i].kind == "word"
                and items[i].text in {"keywords", "abbrevs", "begin"}), len(items))
    imports = [t.text.strip('"') for t in items[start:end]]
    if not imports or any(not re.fullmatch(r"[A-Za-z_0-9./+-]+", name) or ".." in name.split("/")
                          or name.startswith("/") for name in imports):
        raise ValueError("unsupported import; configure a compatible named session dependency")
    return imports


def quote(value: str) -> str:
    return '"' + value.replace("\\", "\\\\").replace('"', '\\"') + '"'


def read_result(path: Path, request: dict, *, returncode: int) -> dict:
    if not path.is_file():
        raise NativeFailure("worker_failure", "native worker produced no structured result; inspect build.log")
    try:
        root = ET.parse(path).getroot()
    except (ET.ParseError, OSError) as exc:
        raise NativeFailure("protocol_error", "partial or malformed native result") from exc
    if (root.tag != "dsp_result" or root.get("schema") != RESULT_VERSION
            or root.get("request_id") != request["request_id"]
            or root.get("input_sha256") != request["input_sha256"]
            or root.get("action") != request["action"]):
        raise NativeFailure("protocol_error", "native result does not match this request")
    if root.get("success") not in {"true", "false"}:
        raise NativeFailure("protocol_error", "native result has no valid success flag")
    if root.get("target_closed") not in {"true", "false"}:
        raise NativeFailure("protocol_error", "invalid target completion flag")
    required = {"proof", "error", "category", "attempts", "settings"}
    if set(child.tag for child in root) != required or any(len(root.findall(name)) != 1 for name in required):
        raise NativeFailure("protocol_error", "missing, repeated or unknown result fields")
    rows = []
    for item in root.findall("attempts/attempt"):
        if item.get("success") not in {"true", "false"}:
            raise NativeFailure("protocol_error", "invalid native attempt status")
        row = dict(item.attrib)
        row["success"] = row["success"] == "true"
        row.update({child.tag: child.text or "" for child in item})
        rows.append(row)
    result = {"success": root.get("success") == "true", "target_closed": root.get("target_closed") == "true",
              "isabelle_proof": root.findtext("proof", ""), "error": root.findtext("error", ""),
              "failure_category": root.findtext("category", "worker_failure"),
              "step_results": rows,
              "prover_settings": {item.get("name"): item.text or "" for item in root.findall("settings/param")},
              "result_path": str(path), "request_id": request["request_id"]}
    if returncode != 0:
        result.update(success=False, failure_category="worker_failure",
                      error=f"native process exited with status {returncode}; " + result["error"])
    if result["success"] and request["action"] == "search" and not result["target_closed"]:
        raise NativeFailure("protocol_error", "native success did not close the selected target")
    if result["success"] and request["action"] == "search":
        result["isabelle_proof"] = normalize_body(result["isabelle_proof"])
    return result


class NativeSearch:
    def __init__(self, config: DspConfig, *, process_factory=OwnedProcess):
        self.config = config
        self.process_factory = process_factory

    def build_command(self, directory: Path, session: str, *, parent_dir=None, heap=False) -> list[str]:
        command = [str(self.config.executable), "build", "-j", "1", "-o", "document=false",
                   "-o", "parallel_proofs=0", "-o", "threads=" + str(self.config.threads)]
        if heap:
            command.append("-b")
        for root in self.config.session_roots:
            command += ["-d", str(repo_path(root))]
        if parent_dir is not None:
            command += ["-d", str(parent_dir)]
        return command + ["-d", str(directory), session]

    def run_build(self, directory: Path, session: str, *, timeout_s: float, deadline: float,
                  parent_dir=None, heap=False) -> int:
        command = self.build_command(directory, session, parent_dir=parent_dir, heap=heap)
        (directory / "command.json").write_text(json.dumps(command, indent=2) + "\n", encoding="utf-8")
        return self.process_factory(command, directory=directory, env=self.config.environment(),
                                    log_path=directory / "build.log", timeout_s=timeout_s,
                                    deadline=deadline).run()

    def infrastructure(self, *, deadline: float) -> tuple[Path, str]:
        identity = fingerprint({"adapter": adapter_hashes(), "base_session": self.config.base_session})[:16]
        name = "DSP_Native_" + identity
        directory = repo_path(RUNTIME_DIR) / "infrastructure" / identity
        directory.mkdir(parents=True, exist_ok=True)
        for source in NATIVE_DIR.iterdir():
            if source.suffix in {".thy", ".ML"}:
                destination = directory / source.name
                if not destination.is_file() or destination.read_bytes() != source.read_bytes():
                    shutil.copyfile(source, destination)
        root = ('session ' + name + ' = ' + quote(self.config.base_session) +
                ' +\n  options [document = false]\n  theories [global] DSP_Native\n')
        (directory / "ROOT").write_text(root, encoding="utf-8")
        # isabelle build validates heap freshness; no success marker substitutes for that check.
        code = self.run_build(directory, name, timeout_s=self.config.startup_timeout_s,
                              deadline=deadline, heap=True)
        if code:
            raise NativeFailure("capability_error", "native infrastructure failed to compile; inspect " + str(directory / "build.log"))
        return directory, name

    def encode_symbols(self, text: str) -> str:
        symbols = repo_path(self.config.isabelle_home) / "etc" / "symbols"
        if not symbols.is_file():
            raise NativeFailure("toolchain_error", "missing Isabelle symbol table")
        mapping = {}
        for line in symbols.read_text(encoding="utf-8").splitlines():
            match = re.match(r"(\\<[^>]+>)\s+.*?code:\s*(0x[0-9A-Fa-f]+)", line)
            if match:
                char = chr(int(match[2], 16))
                if ord(char) > 127:
                    mapping.setdefault(char, match[1])
        return "".join(mapping.get(char, char) for char in text)

    def request(self, record: dict, sketch: str, *, directory: Path, action: str,
                heuristics: tuple[str, ...], deadline: float) -> dict:
        context = validate_context(record)
        imports = imports_of(context.prefix)
        if any(name.split("/")[-1].split(".")[-1] == context.theory_name for name in imports):
            raise ValueError("cannot import the masked target theory into native search")
        directory.mkdir(parents=True, exist_ok=True)
        parent_dir, parent_session = self.infrastructure(deadline=deadline)
        forbidden = [d.name for d in inventory_isabelle_declarations(context.template)
                     if d.char_start >= len(context.prefix)]
        request = {"request_id": uuid.uuid4().hex, "action": action,
                   "prefix": context.prefix, "statement": context.statement,
                   "proof_prefix": context.proof_prefix, "sketch": sketch, "depth": str(context.depth),
                   "target_name": record["isabelle_target_name"], "forbidden_names": forbidden,
                   "heuristics": list(heuristics), "provers": self.config.provers,
                   "step_timeout_s": str(self.config.step_timeout_s),
                   "hammer_timeout_s": str(self.config.hammer_timeout_s),
                   "preplay_timeout_s": str(self.config.preplay_timeout_s),
                   "remaining_s": str(max(0.001, deadline - time.monotonic()))}
        request["input_sha256"] = fingerprint(request)
        root = ET.Element("dsp_request", schema=PROTOCOL_VERSION, **{
            k: request[k] for k in ("request_id", "input_sha256", "action")})
        for name, value in request.items():
            if name in {"request_id", "input_sha256", "action"}:
                continue
            node = ET.SubElement(root, name)
            if isinstance(value, (tuple, list)):
                for item in value:
                    ET.SubElement(node, "item").text = self.encode_symbols(str(item))
            elif value is not None:
                node.text = self.encode_symbols(value)
        ET.ElementTree(root).write(directory / "request.xml", encoding="utf-8", xml_declaration=False)
        (directory / "input.json").write_text(json.dumps(request, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
        session = "DSP_Job_" + request["request_id"]
        dependencies = ""
        if self.config.session_dependencies:
            dependencies = "  sessions " + " ".join(quote(x) for x in self.config.session_dependencies) + "\n"
        (directory / "ROOT").write_text('session ' + session + ' = ' + parent_session +
            ' +\n  options [document = false]\n' + dependencies + '  theories DSP_Driver\n', encoding="utf-8")
        driver = ('theory DSP_Driver imports DSP_Native ' + " ".join(quote(x) for x in imports) +
                  '\nbegin\n' + r'ML \<open>DSP_Native.run \<^theory> "request.xml" "result.xml"\<close>' + '\nend\n')
        (directory / "DSP_Driver.thy").write_text(driver, encoding="utf-8")
        (directory / "line_mapping.json").write_text(json.dumps({
            "original_prefix_lines": context.prefix.count("\n") + 1,
            "oracle_lines": context.statement.count("\n") + 1,
            "sketch_lines": sketch.count("\n") + 1,
            "note": "native attempt line numbers are relative to the recorded source section; offsets count Isabelle symbols",
        }, indent=2) + "\n", encoding="utf-8")
        code = self.run_build(directory, session, timeout_s=max(0.001, deadline-time.monotonic()),
                              deadline=deadline, parent_dir=parent_dir)
        result = read_result(directory / "result.xml", request, returncode=code)
        result["search_directory"] = str(directory)
        return result

    def replay(self, record: dict, proof: str, *, directory: Path, deadline: float) -> dict:
        """A fresh build of the reconstructed theory, with no search-helper import."""
        context = validate_context(record)
        proof = normalize_body(proof)
        directory.mkdir(parents=True, exist_ok=True)
        original = context.theory(proof)
        items = tokens(original)
        begin = next(t for t in items if t.kind == "word" and t.text == "begin")
        # Admit only the existing prefix, then explicitly disable background admission before the target.
        source = (original[:begin.end] + "\ndeclare [[quick_and_dirty = true]]\n" +
                  original[begin.end:len(context.prefix)] + "\ndeclare [[quick_and_dirty = false]]\n" +
                  original[len(context.prefix):])
        theory_path = directory / (context.theory_name + ".thy")
        theory_path.write_text(self.encode_symbols(source), encoding="utf-8")
        session = "DSP_Replay_" + uuid.uuid4().hex
        dependencies = ""
        if self.config.session_dependencies:
            dependencies = "  sessions " + " ".join(quote(x) for x in self.config.session_dependencies) + "\n"
        (directory / "ROOT").write_text('session ' + session + ' = ' + quote(self.config.base_session) +
            ' +\n  options [document = false, quick_and_dirty = false]\n' + dependencies +
            '  theories ' + quote(context.theory_name) + '\n', encoding="utf-8")
        code = self.run_build(directory, session, timeout_s=self.config.replay_timeout_s, deadline=deadline)
        return {"success": code == 0, "replay_theory_path": str(theory_path),
                "replay_log_path": str(directory / "build.log"), "returncode": code}
