"""Native Isabelle2026 configuration, release checks and owned process lifecycle."""
from __future__ import annotations

import hashlib
import json
import math
import os
import re
import shlex
import signal
import subprocess
import time
from dataclasses import asdict, dataclass, fields
from pathlib import Path

from ..common import fingerprint, repo_path, repository_commit

NATIVE_DIR = Path(__file__).resolve().parent / "native"
RUNTIME_DIR = "itpeval/.runs/isabelle2026-native"


def hash_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def adapter_hashes() -> dict:
    package = Path(__file__).resolve().parent
    paths = list(NATIVE_DIR.iterdir()) + [package / name for name in (
        "runtime.py", "native_search.py", "checker.py", "input_contract.py")]
    paths += [package.parent / name for name in (
        "theory_context.py", "sanitize_isabelle.py", "isabelle_syntax.py", "prompt.py", "common.py")]
    return {path.name: hash_file(path) for path in paths if path.is_file()}


@dataclass(frozen=True)
class DspConfig:
    isabelle_home: str = "itpeval/_toolchains/Isabelle2026"
    expected_isabelle_version: str = "Isabelle2026"
    backend: str = "isabelle-native"
    base_session: str = "HOL"
    session_roots: tuple[str, ...] = ()
    session_dependencies: tuple[str, ...] = ()
    threads: int = 4
    provers: tuple[str, ...] | None = None
    startup_timeout_s: float = 120
    step_timeout_s: float = 10
    hammer_timeout_s: float = 40
    preplay_timeout_s: float = 10
    target_timeout_s: float = 1200
    replay_timeout_s: float = 1200

    def __post_init__(self):
        if self.backend != "isabelle-native" or self.expected_isabelle_version != "Isabelle2026":
            raise ValueError("v2-dsp requires isabelle-native/Isabelle2026; migrate the old PISA config")
        if isinstance(self.threads, bool) or not isinstance(self.threads, int) or self.threads < 1:
            raise ValueError("threads must be a positive integer")
        for name in ("startup_timeout_s", "step_timeout_s", "hammer_timeout_s", "preplay_timeout_s",
                     "target_timeout_s", "replay_timeout_s"):
            value = getattr(self, name)
            if isinstance(value, bool) or not isinstance(value, (float, int)) or not math.isfinite(value) or value <= 0:
                raise ValueError(name + " must be finite and positive")
        for name in ("session_roots", "session_dependencies"):
            value = getattr(self, name)
            if not isinstance(value, (tuple, list)) or any(not isinstance(x, str) or not x.strip() for x in value):
                raise ValueError(name + " must be a list of nonempty strings")
        for name in [self.base_session, *self.session_dependencies]:
            if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9.+-]*", name):
                raise ValueError("invalid session name")
        if self.provers is not None and (not isinstance(self.provers, (tuple, list)) or not self.provers
                or any(not isinstance(x, str) or not re.fullmatch(r"[A-Za-z_0-9-]+", x) for x in self.provers)):
            raise ValueError("provers must be null (native defaults) or a nonempty list of names")

    @classmethod
    def load(cls, path: str) -> DspConfig:
        with repo_path(path).open(encoding="utf-8") as stream:
            data = json.load(stream)
        if not isinstance(data, dict):
            raise ValueError("DSP configuration must be a JSON object")
        if any(name in data for name in ("pisa_python_path", "pisa_jar", "dsp_repo_root", "port", "java_bin", "server_class")):
            raise ValueError("PISA configuration is obsolete: copy v2_dsp.example.json and install Isabelle2026; "
                             "PISA/JAR/gRPC and the original DSP checkout are no longer used")
        unknown = set(data) - {field.name for field in fields(cls)}
        if unknown:
            raise ValueError("unknown native config fields: " + ", ".join(sorted(unknown)))
        data["isabelle_home"] = str(repo_path(data.get("isabelle_home", cls.isabelle_home)))
        for name in ("session_roots", "session_dependencies", "provers"):
            if name in data and data[name] is not None:
                if not isinstance(data[name], list):
                    raise ValueError(name + " must be a JSON list")
                data[name] = tuple(data[name])
        data["session_roots"] = tuple(str(repo_path(p)) for p in data.get("session_roots", ()))
        return cls(**data)

    @property
    def executable(self) -> Path:
        return repo_path(self.isabelle_home) / "bin" / "isabelle"

    def environment(self) -> dict:
        """Use Isabelle's USER_HOME override; never change OS HOME or existing settings."""
        root = repo_path(RUNTIME_DIR)
        user = root / "user_home"
        settings = user / ".isabelle" / "Isabelle2026" / "etc" / "settings"
        settings.parent.mkdir(parents=True, exist_ok=True)
        temp = root / "tmp"
        temp.mkdir(exist_ok=True)
        expected = "\n".join([
            "# Generated only for this isolated Isabelle2026 runtime.",
            "ISABELLE_TMP_PREFIX=" + shlex.quote(str(temp / "isabelle")),
            "ISABELLE_HEAPS=" + shlex.quote(str(root / "heaps")),
            "ISABELLE_BROWSER_INFO=" + shlex.quote(str(root / "browser_info")),
            "ISABELLE_COMPONENTS_BASE=" + shlex.quote(str(root / "components")), ""])
        if not settings.is_file() or settings.read_text(encoding="utf-8") != expected:
            settings.write_text(expected, encoding="utf-8")
        env = {k: v for k, v in os.environ.items() if not k.startswith("ISABELLE_") and k != "BASH_ENV"}
        env.update(USER_HOME=str(user), ISABELLE_IDENTIFIER="Isabelle2026",
                   TMPDIR=str(temp), TMP=str(temp), TEMP=str(temp))
        return env

    def metadata(self) -> dict:
        if os.name == "nt":
            raise RuntimeError("native Isabelle2026 runs on the Linux lab machine; local dry-run/offline tests are supported")
        home = repo_path(self.isabelle_home)
        if not self.executable.is_file():
            raise FileNotFoundError("Install Isabelle2026 separately at " + str(home))
        release = json.loads((NATIVE_DIR / "release_sources.json").read_text(encoding="utf-8"))
        source_hashes = {}
        for name, expected in release["sha256"].items():
            actual = hash_file(home / name)
            if actual != expected:
                raise ValueError("Isabelle2026 release source mismatch: " + name)
            source_hashes[name] = actual
        env = self.environment()
        def command(*args):
            run = subprocess.run([str(self.executable), *args], env=env, capture_output=True,
                                 text=True, encoding="utf-8", errors="replace", check=True,
                                 timeout=self.startup_timeout_s)
            return run.stdout.strip()
        version = command("version")
        if version != self.expected_isabelle_version:
            raise ValueError(f"expected {self.expected_isabelle_version}; found {version!r}")
        settings = {}
        for name in ("ISABELLE_HOME_USER", "ISABELLE_HEAPS", "ISABELLE_TMP_PREFIX", "ISABELLE_HEAPS_SYSTEM"):
            value = command("getenv", "-b", name)
            repo_path(value)
            settings[name] = value
        distribution_sources = {}
        source_root = home / "src"
        if source_root.is_dir():
            for path in sorted(source_root.rglob("*")):
                if path.is_file() and (path.name in {"ROOT", "ROOTS"} or path.suffix in {".thy", ".ML", ".scala"}):
                    repo_path(path)
                    distribution_sources[str(path.relative_to(home))] = hash_file(path)
        heap_identity = {}
        for variable in ("ISABELLE_HEAPS_SYSTEM", "ISABELLE_HEAPS"):
            heap_root = repo_path(settings[variable])
            for session in (self.base_session, *self.session_dependencies):
                if heap_root.is_dir():
                    for path in sorted(heap_root.rglob(session)):
                        if path.is_file():
                            repo_path(path)
                            heap_identity[str(path)] = hash_file(path)
        dependencies = {}
        for directory in self.session_roots:
            root = repo_path(directory)
            if not (root / "ROOT").is_file() and not (root / "ROOTS").is_file():
                raise FileNotFoundError("session root must contain ROOT or ROOTS: " + str(root))
            for path in sorted(root.rglob("*")):
                if path.is_file() and (path.name in {"ROOT", "ROOTS"} or path.suffix in {".thy", ".ML"}) and not any(
                        part in {".git", "heaps", "browser_info", "__pycache__"} for part in path.relative_to(root).parts):
                    repo_path(path)
                    dependencies[str(path)] = hash_file(path)
        # Track external prover binaries/settings, without retaining huge executable contents.
        components = {}
        contrib = home / "contrib"
        if contrib.is_dir():
            for component in sorted(contrib.iterdir()):
                if component.is_dir() and any(component.name.lower().startswith(prefix) for prefix in
                        ("e-", "vampire-", "verit-", "z3-", "cvc4-", "cvc5-", "spass-", "zipperposition-")):
                    components[component.name] = {str(p.relative_to(component)): hash_file(p)
                        for p in sorted(component.rglob("*")) if p.is_file() and (
                            p.name in {"settings", "VERSION", "version"} or (os.access(p, os.X_OK) and not p.suffix in {".so", ".jar"}))}
        data = {"backend": self.backend, "isabelle_version": version,
                "isabelle_executable": str(self.executable), "release_sources": source_hashes,
                "distribution_components": components, "native_adapter_sha256": adapter_hashes(),
                "distribution_sources_sha256": fingerprint(distribution_sources),
                "distribution_source_file_count": len(distribution_sources), "session_heaps_sha256": heap_identity,
                "session_sources_sha256": dependencies, "settings": settings,
                "itpeval_commit": repository_commit(), "config": asdict(self),
                "background_policy": "earlier_masked_helpers_admitted"}
        data["backend_fingerprint"] = fingerprint(data)
        return data


class OwnedProcess:
    """One process group with a shared deadline; never kill by executable name."""
    def __init__(self, command: list[str], *, directory: Path, env: dict, log_path: Path,
                 timeout_s: float, deadline: float):
        self.command, self.directory, self.env, self.log_path = command, directory, env, log_path
        self.timeout = min(timeout_s, deadline - time.monotonic())
        self.process = None
        self.owned_processes = {}

    @staticmethod
    def process_identity(pid):
        try:
            data = (Path("/proc") / str(pid) / "stat").read_text()
            parts = data[data.rfind(")") + 2:].split()
            return {"start_ticks": parts[19], "group": int(parts[2])}
        except (OSError, ValueError, IndexError):
            return None

    def capture_owned(self):
        if self.process is None or not Path("/proc").is_dir():
            return
        pending = [self.process.pid, *self.owned_processes]
        seen = set()
        while pending:
            pid = pending.pop()
            if pid in seen:
                continue
            seen.add(pid)
            current = self.process_identity(pid)
            previous = self.owned_processes.get(pid)
            if current is None or previous is not None and current["start_ticks"] != previous["start_ticks"]:
                continue
            self.owned_processes[pid] = current
            try:
                children = (Path("/proc") / str(pid) / "task" / str(pid) / "children").read_text()
                pending.extend(int(child) for child in children.split())
            except (OSError, ValueError):
                pass

    def close(self):
        if self.process is None:
            return
        self.capture_owned()
        if os.name == "nt":
            if self.process.poll() is None:
                subprocess.run(["taskkill", "/PID", str(self.process.pid), "/T", "/F"],
                               capture_output=True, timeout=10, check=False)
        else:
            for sig in (signal.SIGTERM, getattr(signal, "SIGKILL", 9)):
                # ATP/ML workers can start their own groups. Track descendants and
                # start times so cleanup cannot signal an unrelated recycled PID.
                live = {pid: identity for pid, identity in self.owned_processes.items()
                        if self.process_identity(pid) == identity}
                groups = {pid for pid, identity in live.items() if identity["group"] == pid}
                if not self.owned_processes or any(identity["group"] == self.process.pid for identity in live.values()):
                    groups.add(self.process.pid)
                for group in groups:
                    try:
                        os.killpg(group, sig)
                    except ProcessLookupError:
                        pass
                for pid, identity in live.items():
                    if identity["group"] not in groups:
                        try:
                            os.kill(pid, sig)
                        except ProcessLookupError:
                            pass
                if sig == signal.SIGTERM:
                    try:
                        self.process.wait(timeout=3)
                    except subprocess.TimeoutExpired:
                        pass
        self.process.wait(timeout=10)
        if self.owned_processes:
            self.log_path.with_suffix(".processes.json").write_text(
                json.dumps(self.owned_processes, indent=2) + "\n", encoding="utf-8")

    def run(self) -> int:
        if self.timeout <= 0:
            raise TimeoutError("native whole-target deadline exceeded")
        self.directory.mkdir(parents=True, exist_ok=True)
        kwargs = {"start_new_session": True} if os.name != "nt" else {
            "creationflags": subprocess.CREATE_NEW_PROCESS_GROUP | subprocess.CREATE_NO_WINDOW}
        try:
            with self.log_path.open("w", encoding="utf-8") as log:
                self.process = subprocess.Popen(self.command, cwd=self.directory, env=self.env,
                                                stdout=log, stderr=subprocess.STDOUT, **kwargs)
                expires = time.monotonic() + self.timeout
                while True:
                    self.capture_owned()
                    remaining = expires - time.monotonic()
                    if remaining <= 0:
                        raise TimeoutError("native build deadline exceeded; inspect " + str(self.log_path))
                    try:
                        return self.process.wait(timeout=min(0.25, remaining))
                    except subprocess.TimeoutExpired:
                        continue
        finally:
            self.close()
