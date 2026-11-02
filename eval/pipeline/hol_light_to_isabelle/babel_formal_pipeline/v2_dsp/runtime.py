"""Pinned original DSP/PISA runtime, with bounded jobs and owned-process cleanup."""
from __future__ import annotations

from dataclasses import asdict, dataclass, field, fields
import hashlib
import json
import math
import os
from pathlib import Path
import re
import shlex
import signal
import subprocess
import sys
import time
import zipfile
import uuid

from ..common import fingerprint, repo_path, repository_commit

PACKAGE = Path(__file__).resolve().parent
PISA_COMMIT = "690eed41fa03fe04ec015bb375c668cd6fd94261"
DSP_COMMIT = "647aa65ca7b89f4e0f7a65dc15b4e64a81af5e80"
RUNTIME_DIR = "itpeval/.runs/isabelle2021-pisa"
PROC_ROOT = Path("/proc")


def hash_file(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def source_hash(path):
    path = Path(path)
    if path.suffix == ".jar":
        return hash_file(path)
    return hashlib.sha256(path.read_text(encoding="utf-8").encode()).hexdigest()


class PisaFailure(RuntimeError):
    def __init__(self, category, message, *, details=None):
        super().__init__(message)
        self.category, self.details = category, details or {}


@dataclass(frozen=True)
class DspConfig:
    backend: str = "dsp-pisa"
    expected_isabelle_version: str = "Isabelle2021"
    isabelle_home: str = "itpeval/_toolchains/Isabelle2021"
    pisa_root: str = "external/Portal-to-ISAbelle"
    java_bin: str = "java"
    port: int = 9000
    startup_timeout_s: float = 600
    step_timeout_s: float = 60
    hammer_timeout_s: float = 60
    target_timeout_s: float = 1800
    theory_imports: dict[str, str] = field(default_factory=dict)

    def __post_init__(self):
        if self.backend != "dsp-pisa" or self.expected_isabelle_version != "Isabelle2021":
            raise ValueError("use the DSP/PISA Isabelle2021 configuration; Isabelle2026 is retired")
        if isinstance(self.port, bool) or not isinstance(self.port, int) or not 1 <= self.port <= 65535:
            raise ValueError("port must be an integer in 1..65535")
        for name in ("startup_timeout_s", "step_timeout_s", "hammer_timeout_s", "target_timeout_s"):
            value = getattr(self, name)
            if isinstance(value, bool) or not isinstance(value, (int, float)) or not math.isfinite(value) or value <= 0:
                raise ValueError(name + " must be finite and positive")
        if not isinstance(self.theory_imports, dict):
            raise ValueError("theory_imports must be a mapping")
        for original, qualified in self.theory_imports.items():
            if (not isinstance(original, str) or not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", original)
                or not isinstance(qualified, str) or not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9.+-]*\." + re.escape(original), qualified)):
                raise ValueError("theory_imports must qualify a bare theory without changing its basename")

    @classmethod
    def load(cls, path):
        data = json.loads(repo_path(path).read_text(encoding="utf-8"))
        if not isinstance(data, dict):
            raise ValueError("DSP config must be a JSON object")
        unknown = set(data) - {f.name for f in fields(cls)}
        if unknown:
            raise ValueError("obsolete/unknown DSP settings: " + ", ".join(sorted(unknown)) +
                             "; copy v2_dsp_2021.example.json")
        for name in ("isabelle_home", "pisa_root"):
            if name in data:
                data[name] = str(repo_path(data[name]))
        return cls(**data)

    @property
    def root(self):
        return repo_path(self.pisa_root)

    @property
    def jar(self):
        return self.root / "target/scala-2.13/PISA-assembly-0.1.jar"

    @property
    def generated(self):
        return self.root / "generated/python"

    @property
    def executable(self):
        return repo_path(self.isabelle_home) / "bin/isabelle"

    def environment(self):
        runtime = repo_path(RUNTIME_DIR)
        user = runtime / "user_home"
        settings = user / ".isabelle/Isabelle2021/etc/settings"
        settings.parent.mkdir(parents=True, exist_ok=True)
        temp = runtime / "tmp"
        temp.mkdir(exist_ok=True)
        text = "\n".join([
            "# Isolated Isabelle2021 settings for original DSP/PISA.",
            "ISABELLE_HEAPS=" + shlex.quote(str(runtime / "heaps")),
            "ISABELLE_TMP_PREFIX=" + shlex.quote(str(temp / "isabelle")),
            "ISABELLE_BROWSER_INFO=" + shlex.quote(str(runtime / "browser_info")), ""])
        if not settings.is_file() or settings.read_text(encoding="utf-8") != text:
            settings.write_text(text, encoding="utf-8")
        env = {k: v for k, v in os.environ.items() if not k.startswith("ISABELLE_") and k != "BASH_ENV"}
        env.update(USER_HOME=str(user), ISABELLE_IDENTIFIER="Isabelle2021", TMPDIR=str(temp), TMP=str(temp), TEMP=str(temp))
        env["PYTHONPATH"] = os.pathsep.join([str(repo_path(".")), str(self.generated), str(self.root / "src/main/python")])
        return env

    def metadata(self):
        if os.name == "nt":
            raise RuntimeError("Run DSP/PISA/Isabelle2021 on the Linux lab host; offline tests work locally")
        actual = subprocess.run(["git", "-C", str(self.root), "rev-parse", "HEAD"],
            check=True, capture_output=True, text=True, timeout=30).stdout.strip()
        if actual != PISA_COMMIT:
            raise ValueError("PISA must be pinned to " + PISA_COMMIT + "; current HEAD=" + actual)
        expected = json.loads((PACKAGE / "upstream/pisa_sources.json").read_text(encoding="utf-8"))
        for name, digest in expected.items():
            if source_hash(self.root / name) != digest:
                raise ValueError("PISA source differs from the pinned original: " + name)
        stamp = json.loads((self.root / "pisa-build.json").read_text(encoding="utf-8"))
        if stamp.get("commit") != PISA_COMMIT or stamp.get("jar_sha256") != hash_file(self.jar):
            raise ValueError("PISA build stamp missing/stale; run prepare_pisa --build")
        if stamp.get("sources") != expected or stamp.get("build_sbt_sha256") != source_hash(self.root / "build.sbt"):
            raise ValueError("PISA build does not match its pinned source/build settings")
        client_hashes = {name: hash_file(self.generated / name) for name in ("server_pb2.py", "server_pb2_grpc.py")}
        if client_hashes != stamp.get("generated_client_sha256"):
            raise ValueError("generated PISA stubs changed; rerun prepare_pisa --build")
        server_class = f"pisa/server/PisaOneStageServer{self.port}.class"
        with zipfile.ZipFile(self.jar) as jar:
            if server_class not in jar.namelist():
                raise ValueError("PISA JAR does not provide port " + str(self.port))
        env = self.environment()
        def command(args):
            run = subprocess.run(args, capture_output=True, text=True, check=True, timeout=self.startup_timeout_s, env=env)
            return (run.stdout or run.stderr).strip()
        version = command([str(self.executable), "version"])
        if version != self.expected_isabelle_version:
            raise ValueError(f"expected Isabelle2021, found {version!r}")
        java = command([self.java_bin, "-version"])
        if not re.search(r'version "11(?:[.\"]|$)', java):
            raise ValueError("original PISA needs Java 11: " + java)
        command([sys.executable, "-c", "import grpc, func_timeout, server_pb2, server_pb2_grpc, PisaFlexibleClient"])
        settings = {name: command([str(self.executable), "getenv", "-b", name])
                    for name in ("ISABELLE_HOME_USER", "ISABELLE_HEAPS", "ISABELLE_TMP_PREFIX")}
        for value in settings.values():
            repo_path(value)
        result = {"backend": "dsp-pisa", "isabelle_version": version, "pisa_commit": actual,
            "dsp_commit": DSP_COMMIT, "itpeval_commit": repository_commit(), "config": asdict(self),
            "java_version": java, "settings": settings, "pisa_jar_sha256": stamp["jar_sha256"],
            "generated_client_sha256": client_hashes, "dsp_checker_sha256": source_hash(PACKAGE / "upstream/checker.py"),
            "adapter_sha256": {name: source_hash(PACKAGE / name) for name in
                ("checker.py", "runtime.py", "pisa_worker.py", "pisa_context.py", "input_contract.py")},
            "replay_enabled": False, "server_limits": "Original PISA: 10s transitions; 40s normalhammer"}
        result["backend_fingerprint"] = fingerprint(result)
        return result


def run_job(config, directory, request):
    """Run the copied checker in an isolated worker; never build/replay a proof."""
    # Original PISA uses these literal strings as its transport framing.
    if any(marker in request["formal"] for marker in ("<SEP>", "<apply to top level state>")):
        raise PisaFailure("context_error" if request["action"] == "context" else "rejected_proof",
                          "theory text contains a reserved PISA protocol delimiter")
    directory.mkdir(parents=True, exist_ok=True)
    request = {**request, "request_id": uuid.uuid4().hex}
    request["input_sha256"] = fingerprint(request)
    request_path = directory / "input.json"
    request_path.write_text(json.dumps({"config": asdict(config), "request": request}, ensure_ascii=False, indent=2), encoding="utf-8")
    command = [sys.executable, "-m", __package__ + ".pisa_worker", str(request_path)]
    (directory / "command.json").write_text(json.dumps(command), encoding="utf-8")
    process = OwnedProcess(command, directory=repo_path("."), env=config.environment(),
        log_path=directory / "worker.log", timeout_s=config.target_timeout_s,
        deadline=time.monotonic() + config.target_timeout_s)
    try:
        code = process.run()
        result = json.loads((directory / "result.json").read_text(encoding="utf-8"))
        if code != 0 or result.get("request_id") != request["request_id"] or result.get("input_sha256") != request["input_sha256"]:
            raise PisaFailure("worker_failure", "PISA worker exited or returned a mismatched result")
        return result
    except (OSError, ValueError, TimeoutError) as exc:
        raise PisaFailure("timeout" if isinstance(exc, TimeoutError) else "worker_failure", str(exc),
                          details={"workdir": str(directory), "worker_log": str(directory / "worker.log")}) from exc


class OwnedProcess:
    """One process group with a shared deadline; never kill by executable name."""
    def __init__(self, command: list[str], *, directory: Path, env: dict, log_path: Path,
                 timeout_s: float, deadline: float, ready_path: Path | None = None,
                 startup_timeout_s: float | None = None):
        self.command, self.directory, self.env, self.log_path = command, directory, env, log_path
        self.timeout, self.deadline = timeout_s, deadline
        if (ready_path is None) != (startup_timeout_s is None):
            raise ValueError("worker readiness path and startup timeout must be supplied together")
        self.ready_path, self.startup_timeout = ready_path, startup_timeout_s
        self.process = None
        self.owned_processes = {}

    @staticmethod
    def process_identity(pid):
        try:
            data = (PROC_ROOT / str(pid) / "stat").read_text()
            parts = data[data.rfind(")") + 2:].split()
            return {"start_ticks": parts[19], "group": int(parts[2])}
        except (OSError, ValueError, IndexError):
            return None

    def capture_owned(self):
        if self.process is None or not PROC_ROOT.is_dir():
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
                tasks = list((PROC_ROOT / str(pid) / "task").iterdir())
            except OSError:
                continue
            # Linux records children per thread. Scala/ML workers can fork from
            # a non-leader thread, so inspecting task/<pid>/children misses them.
            for task in tasks:
                try:
                    children = (task / "children").read_text()
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
                live = {}
                for pid, identity in self.owned_processes.items():
                    current = self.process_identity(pid)
                    if current is not None and current["start_ticks"] == identity["start_ticks"]:
                        live[pid] = current  # A child may have entered a new process group.
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
        started = time.monotonic()
        expires = min(started + self.timeout, self.deadline)
        if expires <= started:
            raise TimeoutError("PISA whole-target deadline exceeded")
        startup_expires = (min(expires, started + self.startup_timeout)
                           if self.startup_timeout is not None else None)
        self.directory.mkdir(parents=True, exist_ok=True)
        kwargs = {"start_new_session": True} if os.name != "nt" else {
            "creationflags": subprocess.CREATE_NEW_PROCESS_GROUP | subprocess.CREATE_NO_WINDOW}
        try:
            with self.log_path.open("w", encoding="utf-8") as log:
                self.process = subprocess.Popen(self.command, cwd=self.directory, env=self.env,
                                                stdout=log, stderr=subprocess.STDOUT, **kwargs)
                while True:
                    self.capture_owned()
                    now = time.monotonic()
                    remaining = expires - now
                    if remaining <= 0:
                        raise TimeoutError("PISA job deadline exceeded; inspect " + str(self.log_path))
                    if startup_expires is not None:
                        if self.ready_path.is_file():
                            startup_expires = None
                        elif now >= startup_expires:
                            raise TimeoutError("PISA worker startup deadline exceeded; inspect " + str(self.log_path))
                        else:
                            remaining = min(remaining, startup_expires - now)
                    try:
                        return self.process.wait(timeout=min(0.25, remaining))
                    except subprocess.TimeoutExpired:
                        continue
        finally:
            self.close()
