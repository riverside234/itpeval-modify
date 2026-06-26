from __future__ import annotations

import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path

try:
    from itpeval.itp import run_itp, RunResult
except ModuleNotFoundError:
    repo_root = Path(__file__).resolve().parents[2]
    sys.path.insert(0, str(repo_root))
    from itpeval.itp import run_itp, RunResult


@dataclass
class VerifyResult:
    ok: bool
    error: str        # empty string on success
    duration_ms: int


def verify(prover: str, code: str, timeout_s: int = 120) -> VerifyResult:
    """Run the generated proof through the target ITP. Returns VerifyResult."""
    t0 = time.monotonic()
    try:
        result: RunResult = run_itp(
            prover=prover,
            code=code,
            mode="raw",
            timeout_s=timeout_s,
        )
        error = ""
        if not result.ok:
            error = (result.stderr or result.stdout or "").strip()
        return VerifyResult(ok=result.ok, error=error, duration_ms=result.duration_ms)
    except subprocess.TimeoutExpired:
        duration_ms = int((time.monotonic() - t0) * 1000)
        return VerifyResult(ok=False, error=f"timeout after {timeout_s}s", duration_ms=duration_ms)
