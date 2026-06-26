#!/usr/bin/env python3
from __future__ import annotations

import argparse
import os
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class RunResult:
    prover: str
    ok: bool
    returncode: int
    duration_ms: int
    command: list[str]
    workdir: Path
    stdout: str
    stderr: str


def _itpeval_root() -> Path:
    return Path(__file__).resolve().parent


def _default_prefix() -> Path:
    root = _itpeval_root()
    env_prefix = os.environ.get("ITPEVAL_PREFIX")
    if env_prefix:
        return Path(env_prefix).expanduser().resolve()
    if str(root).startswith("/efs/"):
        return Path("/tmp/itpeval-toolchains").resolve()
    return (root / "_toolchains").resolve()


def _check_script(prover: str) -> Path:
    return _adapter_dir(prover) / "check.sh"

def _install_script(prover: str) -> Path:
    return _adapter_dir(prover) / "install.sh"


def _adapter_dir(prover: str) -> Path:
    return _itpeval_root() / "provers" / prover


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content if content.endswith("\n") else content + "\n", encoding="utf-8")


def _prepare_task_dir(*, prover: str, code: str, mode: str, task_dir: Path) -> None:
    """
    Creates the minimal file layout expected by the selected prover adapter.

    mode:
      - raw: `code` is treated as the full file contents (except where a wrapper is mandatory).
      - snippet: `code` is inserted into a small skeleton (only where a wrapper is mandatory).
    """
    mode = mode.lower().strip()
    if mode not in {"raw", "snippet"}:
        raise ValueError(f"unknown mode: {mode!r}")

    if prover == "lean4":
        _write_text(task_dir / "Hello.lean", code)
        return

    if prover == "rocq":
        _write_text(task_dir / "hello.v", code)
        return

    if prover == "isabelle":
        if mode == "snippet":
            theory_name = "Hello"
            session_name = "ITPEval_Hello"
            thy = "theory Hello\n  imports Main\nbegin\n\n" + code + "\n\nend\n"
        else:
            stripped = ""
            for line in code.splitlines():
                candidate = line.strip()
                if candidate:
                    stripped = candidate
                    break

            theory_name = "Hello"
            if stripped.startswith("theory "):
                parts = stripped.split()
                if len(parts) > 1:
                    theory_name = parts[1]

            session_name = f"ITPEval_{theory_name}"
            thy = code

        _write_text(
            task_dir / "ROOT",
            f'session "{session_name}" = HOL +\n  theories\n    {theory_name}\n',
        )
        _write_text(task_dir / f"{theory_name}.thy", thy)
        return

    if prover == "hol-light":
        _write_text(task_dir / "hello.ml", code)
        return

    raise NotImplementedError(f"unsupported prover: {prover}")


def run_itp(
    *,
    prover: str,
    code: str | None = None,
    code_path: Path | None = None,
    task_dir: Path | None = None,
    mode: str = "raw",
    prefix: Path | None = None,
    timeout_s: int | None = None,
    ensure_installed: bool = False,
) -> RunResult:
    if prefix is None:
        prefix = _default_prefix()
    prefix = prefix.expanduser().resolve()

    script = _check_script(prover)
    if not script.exists():
        raise FileNotFoundError(f"missing check script: {script}")

    if task_dir is not None:
        workdir = task_dir.expanduser().resolve()
        if not workdir.is_dir():
            raise FileNotFoundError(f"--task-dir is not a directory: {workdir}")
    else:
        if code_path is not None:
            if code is not None:
                raise ValueError("pass only one of code/code_path")
            code = Path(code_path).expanduser().read_text(encoding="utf-8")
        if code is None:
            raise ValueError("provide either code/code_path or --task-dir")
        tmp_root = Path(tempfile.mkdtemp(prefix=f"itpeval-{prover}-"))
        workdir = tmp_root
        _prepare_task_dir(prover=prover, code=code, mode=mode, task_dir=workdir)

    env = os.environ.copy()
    env["ITPEVAL_PREFIX"] = str(prefix)
    env["ITPEVAL_TASK_DIR"] = str(workdir)

    if ensure_installed:
        install_script = _install_script(prover)
        if not install_script.exists():
            raise FileNotFoundError(f"missing install script: {install_script}")
        install_env = env.copy()
        install_env.pop("ITPEVAL_TASK_DIR", None)
        install_log = workdir / ".itpeval.install.log"
        with install_log.open("w", encoding="utf-8") as handle:
            completed_install = subprocess.run(
                ["/bin/bash", str(install_script)],
                env=install_env,
                cwd=str(_itpeval_root()),
                stdout=handle,
                stderr=subprocess.STDOUT,
                check=False,
                text=True,
            )
        if completed_install.returncode != 0:
            try:
                tail = install_log.read_text(encoding="utf-8", errors="replace").splitlines()[-200:]
                tail_text = "\n".join(tail).rstrip()
            except Exception:
                tail_text = "<unable to read install log>"
            raise RuntimeError(
                "\n".join(
                    [
                        f"install failed for prover={prover} rc={completed_install.returncode}",
                        f"install_log={install_log}",
                        "--- last 200 lines ---",
                        tail_text,
                    ]
                ).rstrip()
            )

    started = time.time()
    completed = subprocess.run(
        ["/bin/bash", str(script)],
        env=env,
        cwd=str(workdir),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout_s,
        check=False,
        text=True,
    )
    duration_ms = int((time.time() - started) * 1000)
    ok = completed.returncode == 0
    return RunResult(
        prover=prover,
        ok=ok,
        returncode=int(completed.returncode),
        duration_ms=duration_ms,
        command=["/bin/bash", str(script)],
        workdir=workdir,
        stdout=completed.stdout,
        stderr=completed.stderr,
    )


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="itp.py",
        description="One-file unified runner for ITPEval prover adapters.",
    )
    parser.add_argument("--prover", required=True, help="prover name (e.g. lean4, rocq, isabelle, hol-light)")
    parser.add_argument(
        "--mode",
        default="raw",
        choices=("raw", "snippet"),
        help="how to interpret --code/--file (default: raw)",
    )
    parser.add_argument("--prefix", default=None, help="toolchain prefix (defaults to ITPEVAL_PREFIX or itpeval/_toolchains)")
    parser.add_argument("--timeout-s", type=int, default=None, help="timeout in seconds")
    parser.add_argument(
        "--ensure-installed",
        action="store_true",
        help="run the prover's install.sh before checking (useful for one-file usage)",
    )

    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--code", default=None, help="inline code (file contents or snippet)")
    source.add_argument("--file", default=None, help="path to a code file to run")
    source.add_argument("--task-dir", default=None, help="pre-built task directory to run (must match prover's check.sh expectations)")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = _build_parser().parse_args(argv)
    prefix = Path(args.prefix).expanduser().resolve() if args.prefix else None
    code_path = Path(args.file) if args.file else None
    task_dir = Path(args.task_dir) if args.task_dir else None
    try:
        result = run_itp(
            prover=args.prover,
            code=args.code,
            code_path=code_path,
            task_dir=task_dir,
            mode=args.mode,
            prefix=prefix,
            timeout_s=args.timeout_s,
            ensure_installed=bool(args.ensure_installed),
        )
    except subprocess.TimeoutExpired as exc:
        print(f"[ITPEval] TIMEOUT after {args.timeout_s}s: {exc}", file=sys.stderr)
        return 2
    except Exception as exc:
        print(f"[ITPEval] ERROR: {exc}", file=sys.stderr)
        return 2

    stream = sys.stdout if result.ok else sys.stderr
    print(f"[ITPEval] prover={result.prover} ok={result.ok} rc={result.returncode} ms={result.duration_ms}", file=stream)
    if result.stdout.strip():
        print("--- stdout ---", file=stream)
        print(result.stdout.rstrip(), file=stream)
    if result.stderr.strip():
        print("--- stderr ---", file=stream)
        print(result.stderr.rstrip(), file=stream)
    print(f"[ITPEval] workdir={result.workdir}", file=stream)
    return 0 if result.ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
