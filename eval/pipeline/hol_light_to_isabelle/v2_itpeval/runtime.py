"""Resolve the exact ITPEval installation used for both version checks and builds."""

from __future__ import annotations

import subprocess

from itpeval.itp import _default_prefix
from eval.pipeline.hol_light_to_isabelle.common import repository_commit


def isabelle2024_runtime() -> dict:
    prefix = _default_prefix().resolve()
    executable = prefix / "isabelle" / "bin" / "isabelle"
    if not executable.is_file():
        raise FileNotFoundError(f"missing Isabelle2024 executable: {executable}")
    run = subprocess.run([str(executable), "version"], text=True, capture_output=True,
                         timeout=30, check=True)
    version = run.stdout.strip()
    if version != "Isabelle2024":
        raise ValueError(f"v2-itpeval requires Isabelle2024; found {version!r}")
    return {"backend": "itpeval", "isabelle_version": version,
            "itpeval_commit": repository_commit(),
            "isabelle_executable": str(executable.resolve()), "prefix": str(prefix)}
