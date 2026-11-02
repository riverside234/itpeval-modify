"""Isolated execution of the copied DSP checker using the original PISA client."""
from __future__ import annotations
import json
import socket
import subprocess
import sys
import time
from pathlib import Path

from .runtime import DspConfig, PisaFailure
from .upstream.checker import Checker as OriginalChecker


class BoundedStub:
    """RPC deadlines and logging only; proof execution stays in upstream PISA."""
    def __init__(self, stub, config, directory, deadline):
        self.stub, self.config, self.directory, self.deadline = stub, config, directory, deadline
        self.last_error = ""

    def __getattr__(self, name):
        rpc = getattr(self.stub, name)
        def call(request):
            action = getattr(request, "command", "")
            budget = (self.config.startup_timeout_s if name != "IsabelleCommand" or action.startswith("<parse text>") else
                      self.config.hammer_timeout_s if "normalhammer" in action else self.config.step_timeout_s)
            remaining = min(budget, self.deadline - time.monotonic())
            if remaining <= 0:
                raise TimeoutError("DSP target deadline exhausted")
            event = {"rpc": name, "request": str(request), "timeout_s": remaining}
            try:
                response = rpc(request, timeout=remaining)
                event["response"] = str(response)
                return response
            except Exception as exc:
                event["error"] = self.last_error = f"{type(exc).__name__}: {exc}"
                raise
            finally:
                with (self.directory / "rpc.jsonl").open("a", encoding="utf-8") as stream:
                    stream.write(json.dumps(event, ensure_ascii=False) + "\n")
        return call


class ObservedChecker(OriginalChecker):
    """Keep original DSP heuristics/normalhammer; add diagnostics and a context gate."""
    def __init__(self, *args, force_hammer=False, **kwargs):
        super().__init__(*args, **kwargs)
        self.force_hammer, self.in_gap = force_hammer, False
        self.attempts, self.env = [], None

    def _initialize(self):
        env = super()._initialize()
        self.env = env
        ancestors = env.post("<get_ancestors>").split(",")
        if Path(self.theory_file).stem in {name.strip().split(".")[-1] for name in ancestors}:
            raise PisaFailure("context_error", "selected target theory is already inherited from the parent/imports")
        return env

    def _exit(self, env):
        # The worker owns the JVM; its parent owns and cleans up all descendants.
        # Keep the state for the context-only goal check below until worker cleanup.
        self.env = env

    def _run_step(self, step, i, tls_name, env):
        started = time.monotonic()
        mode = "hammer" if step.strip().startswith("normalhammer") else "heuristic" if self.in_gap else "search"
        try:
            result = super()._run_step(step, i, tls_name, env)
            self.attempts.append({"mode": mode, "command": step, "success": result[4] is None,
                                  "observation": result[0], "duration_seconds": time.monotonic()-started})
            return result
        except Exception as exc:
            self.attempts.append({"mode": mode, "command": step, "success": False, "error": str(exc)})
            raise

    def _run_sledgehammer(self, step, i, tls_name, env):
        self.in_gap = True
        try:
            if self.force_hammer:  # Lab capability control only; production uses super().
                return self._run_step(step.replace("sledgehammer", "normalhammer"), i, tls_name, env)
            return super()._run_sledgehammer(step, i, tls_name, env)
        finally:
            self.in_gap = False


def execute(config, request, directory):
    import grpc
    import PisaFlexibleClient as client
    import server_pb2_grpc
    # Fail before starting/connecting to another user's server on an occupied port.
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", config.port))
    working = directory / "miniF2F"  # Original PISA's supported HOL session layout.
    working.mkdir()
    theory = working / (request["theory_name"] + ".thy")
    theory.write_text(request["formal"], encoding="utf-8")
    deadline = time.monotonic() + config.target_timeout_s
    checker = None
    channel = grpc.insecure_channel(f"localhost:{config.port}", options=[
        ("grpc.max_send_message_length", 100 * 1024 * 1024),
        ("grpc.max_receive_message_length", 100 * 1024 * 1024)])
    command = [config.java_bin, "-cp", str(config.jar), f"pisa.server.PisaOneStageServer{config.port}"]
    (directory / "server_command.json").write_text(json.dumps(command), encoding="utf-8")
    with (directory / "pisa-server.log").open("w", encoding="utf-8") as log:
        server = subprocess.Popen(command, cwd=working, stdout=log, stderr=subprocess.STDOUT)
        try:
            grpc.channel_ready_future(channel).result(timeout=min(config.startup_timeout_s, config.target_timeout_s))
            if server.poll() is not None:
                raise RuntimeError("owned PISA server exited during startup")
            client.create_stub = lambda port: BoundedStub(server_pb2_grpc.ServerStub(channel), config, directory, deadline)
            checker = ObservedChecker(str(working), str(config.executable.parent.parent), str(theory),
                                      port=config.port, force_hammer=request.get("force_hammer", False))
            raw = checker.check(request["formal"])
            if request["action"] == "context":
                level = checker.env.post("<get_proof_level> " + raw["final_state"]).strip()
                success = not raw["reason"] and raw["last_step"] == raw["num_steps"] and level.isdecimal() and int(level) > 0
                raw.update(success=success, context_ready=success, proof_level=level)
            return {"success": raw["success"], "error": raw["reason"], "dsp_result": raw,
                    "step_results": checker.attempts,
                    "failure_category": None if raw["success"] else
                        "context_error" if request["action"] == "context" else "proof_failure"}
        finally:
            if checker is not None and checker.env is not None:
                # Bounded RPC; process ownership cleanup also runs on timeout/failure.
                checker.env.stub.deadline = min(checker.env.stub.deadline, time.monotonic() + 2)
                OriginalChecker._exit(checker, checker.env)
            channel.close()
            server.terminate()
            try:
                server.wait(timeout=3)
            except subprocess.TimeoutExpired:
                server.kill()
                server.wait(timeout=3)


def main():
    path = Path(sys.argv[1])
    data = json.loads(path.read_text(encoding="utf-8"))
    request = data["request"]
    started = time.monotonic()
    try:
        result = execute(DspConfig(**data["config"]), request, path.parent)
    except Exception as exc:
        result = {"success": False, "error": f"{type(exc).__name__}: {exc}",
                  "failure_category": exc.category if isinstance(exc, PisaFailure) else "context_error" if request["action"] == "context" else "worker_failure",
                  "step_results": []}
    result.update(request_id=request["request_id"], input_sha256=request["input_sha256"],
                  duration_seconds=time.monotonic()-started)
    (path.parent / "result.json").write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
