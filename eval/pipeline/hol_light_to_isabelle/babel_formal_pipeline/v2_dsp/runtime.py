"""Optional PISA runtime with bounded RPCs and cleanup of owned processes only."""

from __future__ import annotations

import hashlib
import importlib
import json
import os
import re
import signal
import socket
import subprocess
import sys
import time
from dataclasses import asdict, dataclass
from pathlib import Path

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.common import fingerprint, repo_path, repository_commit


@dataclass(frozen=True)
class DspConfig:
    dsp_repo_root: str | None
    pisa_python_path: str
    pisa_jar: str
    isabelle_home: str
    expected_isabelle_version: str
    java_bin: str = "java"
    port: int = 9000
    step_timeout_s: float = 60
    hammer_timeout_s: float = 60
    target_timeout_s: float = 1200
    startup_timeout_s: float = 120
    server_class: str = "pisa.server.PisaOneStageServer{port}"
    expected_dsp_commit: str = "647aa65ca7b89f4e0f7a65dc15b4e64a81af5e80"
    expected_pisa_commit: str = "56def2c39f85d211e1f40cc5765581a567879106"
    check_dsp_repo: bool = False

    @classmethod
    def load(cls, path: str) -> DspConfig:
        with repo_path(path).open(encoding="utf-8") as handle:
            data = json.load(handle)
        if not isinstance(data, dict):
            raise ValueError("DSP configuration must be a JSON object")
        check_dsp_repo = data.get("check_dsp_repo", False)
        if not isinstance(check_dsp_repo, bool):
            raise ValueError("check_dsp_repo must be a boolean")
        data.setdefault("dsp_repo_root", None)
        paths = ["pisa_python_path", "pisa_jar", "isabelle_home"]
        if check_dsp_repo:
            paths.append("dsp_repo_root")
        for name in paths:
            if name not in data or not isinstance(data[name], str) or not data[name].strip():
                raise ValueError("missing dependency path: " + name)
            value = Path(os.path.expandvars(data[name])).expanduser()
            if not value.is_absolute():
                value = repo_path(value)
            data[name] = str(value.resolve())
        config = cls(**data)
        if not isinstance(config.port, int) or isinstance(config.port, bool) or not 1 <= config.port <= 65535:
            raise ValueError("invalid PISA port")
        for name in ("step_timeout_s", "hammer_timeout_s", "target_timeout_s", "startup_timeout_s"):
            value = getattr(config, name)
            if isinstance(value, bool) or not isinstance(value, (float, int)) or value <= 0:
                raise ValueError(name + " must be positive")
        commits = ["expected_pisa_commit"]
        if config.check_dsp_repo:
            commits.append("expected_dsp_commit")
        for name in commits:
            if not re.fullmatch(r"[0-9a-f]{40}", getattr(config, name)):
                raise ValueError(name + " must pin a full Git commit")
        return config

    def metadata(self) -> dict:
        directories = ["pisa_python_path", "isabelle_home"]
        if self.check_dsp_repo:
            if not self.dsp_repo_root:
                raise ValueError("check_dsp_repo requires dsp_repo_root")
            directories.append("dsp_repo_root")
        for name in directories:
            if not Path(getattr(self, name)).is_dir():
                raise FileNotFoundError(f"{name}: {getattr(self, name)}")
        jar = Path(self.pisa_jar)
        if not jar.is_file():
            raise FileNotFoundError(f"PISA JAR not found: {jar}")
        commits = {"dsp_commit": None, "dsp_repo_checked": self.check_dsp_repo}
        checks = [("pisa", self.pisa_python_path, self.expected_pisa_commit)]
        if self.check_dsp_repo:
            checks.append(("dsp", self.dsp_repo_root, self.expected_dsp_commit))
        for label, directory, expected in checks:
            run = subprocess.run(["git", "-C", directory, "rev-parse", "HEAD"], text=True,
                                 capture_output=True, check=True, timeout=30)
            actual = run.stdout.strip()
            if actual != expected:
                raise ValueError(f"{label} commit mismatch: expected {expected}, found {actual}")
            commits[label + "_commit"] = actual
        executable = Path(self.isabelle_home) / "bin" / "isabelle"
        version = subprocess.run([str(executable), "version"], text=True, capture_output=True,
                                 check=True, timeout=30).stdout.strip()
        if version != self.expected_isabelle_version:
            raise ValueError(f"expected {self.expected_isabelle_version}; found {version!r}")
        java = subprocess.run([self.java_bin, "-version"], text=True, capture_output=True,
                              check=True, timeout=30)
        digest = hashlib.sha256()
        with jar.open("rb") as handle:
            for block in iter(lambda: handle.read(1024 * 1024), b""):
                digest.update(block)
        client_hashes = {}
        for name in ("server_pb2.py", "server_pb2_grpc.py"):
            source = Path(self.pisa_python_path) / name
            client_hashes[name] = hashlib.sha256(source.read_bytes()).hexdigest()
        return {
            "backend": "dsp-pisa", **commits, "isabelle_version": version,
            "itpeval_commit": repository_commit(),
            "isabelle_executable": str(executable.resolve()), "java_version": (
                java.stderr or java.stdout).strip(),
            "pisa_jar_sha256": digest.hexdigest(), "pisa_client_sha256": client_hashes,
            "config": asdict(self), "config_sha256": fingerprint(asdict(self)),
            "server_internal_limits": "upstream normalhammer 40s; ordinary transition 10s",
        }


def has_error(output: str) -> bool:
    return bool(re.search(
        r"(?im)^\s*(?:error:|step error|unknown error|didn't find|unrecognised operation)",
        output))


class PisaSession:
    """One owned JVM and its Isabelle process, using the upstream protobuf API."""

    def __init__(self, config: DspConfig, directory: Path, theory_name: str,
                 template: str, *, deadline: float):
        self.config = config
        # Upstream PisaOS uses this path component to select its HOL session.
        self.directory = directory / "miniF2F"
        self.directory.mkdir(parents=True, exist_ok=True)
        self.theory_path = self.directory / (theory_name + ".thy")
        self.theory_path.write_text(template, encoding="utf-8")
        self.deadline = deadline
        self.process = self.channel = self.log = None

    def remaining(self, budget: float) -> float:
        remaining = min(budget, self.deadline - time.monotonic())
        if remaining <= 0:
            raise TimeoutError("DSP per-target deadline exceeded")
        return remaining

    def __enter__(self):
        try:
            import grpc
            self.grpc = grpc
            source = str(Path(self.config.pisa_python_path).resolve())
            sys.path.insert(0, source)
            try:
                self.pb = importlib.import_module("server_pb2")
                api = importlib.import_module("server_pb2_grpc")
                for module in (self.pb, api):
                    if Path(module.__file__).resolve().parent != Path(source):
                        raise RuntimeError("another PISA protobuf module is already loaded")
            finally:
                sys.path.remove(source)
            with socket.socket() as port:
                port.bind(("127.0.0.1", self.config.port))
            self.log = (self.directory / "pisa-server.log").open("w", encoding="utf-8")
            kwargs = {"start_new_session": True} if os.name != "nt" else {
                "creationflags": subprocess.CREATE_NEW_PROCESS_GROUP | subprocess.CREATE_NO_WINDOW}
            self.process = subprocess.Popen(
                [self.config.java_bin, "-cp", self.config.pisa_jar,
                 self.config.server_class.format(port=self.config.port)],
                cwd=self.directory, stdout=self.log, stderr=subprocess.STDOUT, **kwargs)
            self.channel = grpc.insecure_channel(
                f"127.0.0.1:{self.config.port}",
                options=[("grpc.max_receive_message_length", 100 * 1024 * 1024),
                         ("grpc.max_send_message_length", 100 * 1024 * 1024)])
            try:
                grpc.channel_ready_future(self.channel).result(
                    timeout=self.remaining(self.config.startup_timeout_s))
            except grpc.FutureTimeoutError as exc:
                raise TimeoutError("PISA server startup deadline exceeded") from exc
            if self.process.poll() is not None:
                raise RuntimeError("PISA server exited; inspect pisa-server.log")
            self.stub = api.ServerStub(self.channel)
            for method, request in (
                (self.stub.InitialiseIsabelle, self.pb.IsaPath(path=self.config.isabelle_home)),
                (self.stub.IsabelleWorkingDirectory, self.pb.IsaPath(path=str(self.directory))),
                (self.stub.IsabelleContext, self.pb.IsaContext(context=str(self.theory_path))),
            ):
                method(request, timeout=self.remaining(self.config.startup_timeout_s))
            self.post("<initialise>")
            return self
        except BaseException:
            self.close()
            raise

    def post(self, command: str, *, timeout_s: float | None = None) -> str:
        try:
            output = self.stub.IsabelleCommand(
                self.pb.IsaCommand(command=command),
                timeout=self.remaining(timeout_s or self.config.step_timeout_s)).state
        except self.grpc.RpcError as exc:
            if exc.code() == self.grpc.StatusCode.DEADLINE_EXCEEDED:
                raise TimeoutError("PISA RPC deadline exceeded") from exc
            raise RuntimeError(f"PISA RPC failed: {exc}") from exc
        if has_error(output):
            raise RuntimeError(output)
        return output

    def parse(self, text: str) -> list[str]:
        output = self.post("<parse text> " + text)
        steps = [step.strip() for step in output.split("<SEP>") if step.strip()]
        if not steps:
            raise ValueError("PISA returned no parsed commands")
        return steps

    def step(self, command: str, old: str, new: str, *, hammer: bool = False) -> str:
        if "<apply to top level state>" in command or "<SEP>" in command:
            raise ValueError("reserved PISA protocol delimiter in proof")
        return self.post(
            f"<apply to top level state> {old} <apply to top level state> "
            f"{command} <apply to top level state> {new}",
            timeout_s=self.config.hammer_timeout_s if hammer else self.config.step_timeout_s)

    def finished(self, state: str) -> bool:
        result = self.post("<is finished> " + state).strip()
        if result not in {"true", "false"}:
            raise RuntimeError("invalid PISA completion response: " + result)
        return result == "true"

    def close(self) -> None:
        if self.channel is not None:
            self.channel.close()
        if self.process is not None:
            if os.name == "nt":
                if self.process.poll() is None:
                    subprocess.run(["taskkill", "/PID", str(self.process.pid), "/T", "/F"],
                                   capture_output=True, timeout=10, check=False)
            else:
                try:
                    os.killpg(self.process.pid, signal.SIGTERM)
                except ProcessLookupError:
                    pass
                try:
                    self.process.wait(timeout=3)
                except subprocess.TimeoutExpired:
                    pass
                try:
                    os.killpg(self.process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
            self.process.wait(timeout=10)
        if self.log is not None:
            self.log.close()

    def __exit__(self, *exc):
        self.close()
