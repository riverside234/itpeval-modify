"""Full-session native jobs, strict XML protocol and checked target completion."""
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
from ..theory_context import validate_context
from .input_contract import normalize_proof, normalize_sketch
from .runtime import DspConfig, NATIVE_DIR, RUNTIME_DIR, OwnedProcess, adapter_hashes

PROTOCOL_VERSION = "dsp_native_request_v1"
RESULT_VERSION = "dsp_native_result_v1"


class NativeFailure(RuntimeError):
    def __init__(self, category: str, message: str, *, details: dict | None = None):
        super().__init__(message)
        self.category = category
        self.details = details or {}


def import_tokens(prefix: str) -> list:
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
    return items[start:end]


def imports_of(prefix: str) -> list[str]:
    return [item.text.strip('"') for item in import_tokens(prefix)]


def resolve_imports(source: str, config: DspConfig, *, theory_name: str) -> tuple[str, dict]:
    """Qualify configured imports only; never import a replacement target theory."""
    items = import_tokens(source)
    original = [item.text.strip('"') for item in items]
    resolved = [config.theory_imports.get(name, name) for name in original]
    def basename(name):
        leaf = name.rsplit("/", 1)[-1]
        return (leaf[:-4] if leaf.endswith(".thy") else leaf).rsplit(".", 1)[-1]
    if any(basename(name) == theory_name for name in resolved):
        raise NativeFailure("context_error", "cannot import the selected target theory into native search")
    sessions = list(config.session_dependencies)
    for name in resolved:
        # Dotted theory names identify their owning session. File paths and
        # global names such as Main do not. Isabelle resolves the transitive graph.
        if "/" not in name and "." in name and not name.endswith(".thy"):
            session = name.rsplit(".", 1)[0]
            if session != config.base_session and session not in sessions:
                sessions.append(session)
    # Token offsets preserve comments, original line numbers and all declarations.
    # Stored dataset templates, proof spans and hashes are never edited.
    for item, before, after in reversed(list(zip(items, original, resolved))):
        if before != after:
            source = source[:item.start] + quote(after) + source[item.end:]
    return source, {"original_imports": original, "resolved_imports": resolved,
                    "session_dependencies": sessions}


def session_clause(resolution: dict) -> str:
    sessions = resolution["session_dependencies"]
    return "  sessions " + " ".join(quote(name) for name in sessions) + "\n" if sessions else ""


def build_diagnostics(directory: Path, returncode: int | None) -> dict:
    path = directory / "build.log"
    excerpt = ""
    if path.is_file():
        with path.open("rb") as stream:
            stream.seek(0, 2)
            stream.seek(max(0, stream.tell() - 16000))
            excerpt = stream.read().decode("utf-8", errors="replace").strip()
    return {"build_log_path": str(path), "build_returncode": returncode,
            "build_log_excerpt": excerpt}


def build_error(message: str, diagnostics: dict) -> str:
    return (message + f" (exit status {diagnostics['build_returncode']}); "
            + diagnostics["build_log_path"]
            + ("\n" + diagnostics["build_log_excerpt"] if diagnostics["build_log_excerpt"] else ""))


def quote(value: str) -> str:
    return '"' + value.replace("\\", "\\\\").replace('"', '\\"') + '"'


def read_result(path: Path, request: dict, *, returncode: int) -> dict:
    if not path.is_file():
        details = build_diagnostics(path.parent, returncode)
        log = details["build_log_excerpt"]
        category = "import_error" if any(marker in log for marker in (
            "Cannot load theory", "Bad import of theory", "Bad imports session",
            "Unknown session", "Undefined session", "need to include sessions")) else "worker_failure"
        raise NativeFailure(category, build_error("native worker produced no structured result", details),
                            details=details)
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
        details = build_diagnostics(path.parent, returncode)
        result.update(details, success=False, failure_category="worker_failure",
                      error=build_error("native process failed; " + result["error"], details))
    if result["success"] and request["action"] == "search" and not result["target_closed"]:
        raise NativeFailure("protocol_error", "native success did not close the selected target")
    if result["success"] and request["action"] == "search":
        result["isabelle_proof"] = normalize_proof(result["isabelle_proof"])
    return result


class NativeSearch:
    def __init__(self, config: DspConfig, *, process_factory=OwnedProcess):
        self.config = config
        self.process_factory = process_factory

    def build_command(self, directory: Path, session: str, *, parent_dir=None, heap=False) -> list[str]:
        command = [str(self.config.executable), "build", "-j", "1", "-o", "document=false",
                   "-o", "parallel_proofs=0", "-o", "timeout_scale=1.0", "-o", "threads=" + str(self.config.threads)]
        if heap:
            command.append("-b")
        for root in self.config.session_roots:
            command += ["-d", str(repo_path(root))]
        if parent_dir is not None:
            command += ["-d", str(parent_dir)]
        return command + ["-d", str(directory), session]

    def run_build(self, directory: Path, session: str, *, timeout_s: float, deadline: float,
                  parent_dir=None, heap=False, ready_path: Path | None = None) -> int:
        command = self.build_command(directory, session, parent_dir=parent_dir, heap=heap)
        (directory / "command.json").write_text(json.dumps(command, indent=2) + "\n", encoding="utf-8")
        startup = ({} if ready_path is None else
                   {"ready_path": ready_path, "startup_timeout_s": self.config.startup_timeout_s})
        process = self.process_factory(command, directory=directory, env=self.config.environment(),
                                       log_path=directory / "build.log", timeout_s=timeout_s,
                                       deadline=deadline, **startup)
        try:
            return process.run()
        except (TimeoutError, OSError) as exc:
            # OwnedProcess has already cleaned up its workers. Preserve the log
            # even if the ML job never had time to produce result.xml.
            code = getattr(getattr(process, "process", None), "returncode", None)
            details = build_diagnostics(directory, code)
            details.update(build_directory=str(directory), build_session=session)
            category = "timeout" if isinstance(exc, TimeoutError) else "worker_failure"
            raise NativeFailure(category, build_error(str(exc), details), details=details) from exc

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
                ' +\n  options [document = false]\n  theories DSP_Native (global)\n')
        (directory / "ROOT").write_text(root, encoding="utf-8")
        # isabelle build validates heap freshness; no success marker substitutes for that check.
        code = self.run_build(directory, name, timeout_s=self.config.startup_timeout_s,
                              deadline=deadline, heap=True)
        if code:
            details = build_diagnostics(directory, code)
            raise NativeFailure("capability_error", build_error("native infrastructure failed to compile", details),
                                details=details)
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
        if action not in {"context", "search"}:
            raise ValueError("unsupported native action")
        if action == "search":
            sketch = normalize_sketch(sketch)
        prefix, resolution = resolve_imports(context.prefix, self.config, theory_name=context.theory_name)
        imports = resolution["resolved_imports"]
        external_sessions = sorted(set(resolution["session_dependencies"]) &
                                   {"Triangle", "Cayley_Hamilton", "Pratt_Certificate"})
        if external_sessions and not self.config.session_roots:
            raise NativeFailure("import_error",
                "Missing AFP session roots for " + ", ".join(external_sessions) +
                ". Install the AFP release matching Isabelle2026 under this repository and "
                "add its thys directory to session_roots (or lab_preflight --afp-root). "
                "Keep base_session=HOL to avoid importing existing target proofs.",
                details={"import_resolution": resolution, "required_afp_sessions": external_sessions})
        directory.mkdir(parents=True, exist_ok=True)
        (directory / "import_resolution.json").write_text(json.dumps(resolution, indent=2) + "\n", encoding="utf-8")
        parent_dir, parent_session = self.infrastructure(deadline=deadline)
        forbidden = [d.name for d in inventory_isabelle_declarations(context.template)
                     if d.char_start >= len(context.prefix)]
        request = {"request_id": uuid.uuid4().hex, "action": action,
                   "prefix": prefix, "statement": context.statement,
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
        dependencies = session_clause(resolution)
        (directory / "ROOT").write_text('session ' + session + ' = ' + parent_session +
            ' +\n  options [document = false]\n' + dependencies + '  theories DSP_Driver\n', encoding="utf-8")
        # A request-specific marker separates worker/session startup from proof search.
        ready_name = "ready-" + request["request_id"]
        driver = ('theory DSP_Driver imports DSP_Native ' + " ".join(quote(x) for x in imports) +
                  '\nbegin\n' + r'ML \<open>' + '\n' +
                  'val _ = File.write (Path.explode "' + ready_name + '") "ready";\n' +
                  r'val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";' + '\n' +
                  r'\<close>' + '\nend\n')
        (directory / "DSP_Driver.thy").write_text(driver, encoding="utf-8")
        (directory / "line_mapping.json").write_text(json.dumps({
            "original_prefix_lines": context.prefix.count("\n") + 1,
            "oracle_lines": context.statement.count("\n") + 1,
            "sketch_lines": sketch.count("\n") + 1,
            "note": "native attempt line numbers are relative to the recorded source section; offsets count Isabelle symbols",
        }, indent=2) + "\n", encoding="utf-8")
        code = self.run_build(directory, session, timeout_s=max(0.001, deadline-time.monotonic()),
                              deadline=deadline, parent_dir=parent_dir, ready_path=directory / ready_name)
        try:
            result = read_result(directory / "result.xml", request, returncode=code)
        except NativeFailure as exc:
            exc.details.update(search_directory=str(directory), import_resolution=resolution)
            raise
        result["search_directory"] = str(directory)
        result["import_resolution"] = resolution
        return result
