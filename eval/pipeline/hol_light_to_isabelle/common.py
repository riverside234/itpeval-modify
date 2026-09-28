from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any, Iterable

from eval.pipeline.config import REPO_ROOT


LAB_REPO_ROOT = "/data/not_backed_up/yxu209/ITPEval"
RESULTS_DIR = "eval/results/hol_light_to_isabelle_v2"


def validate_layout(expected_root: str | None = None) -> Path:
    root = REPO_ROOT.resolve()
    if expected_root and root != Path(expected_root).expanduser().resolve():
        raise ValueError(f"expected repository {expected_root}, found {root}")
    for name in ("eval/data/proofs.json", "eval/data/stmts.json"):
        if not (root / name).is_file():
            raise FileNotFoundError(root / name)
    return root


def repo_path(path: str | Path) -> Path:
    root = REPO_ROOT.resolve()
    candidate = Path(path).expanduser()
    resolved = (candidate if candidate.is_absolute() else root / candidate).resolve()
    if not resolved.is_relative_to(root):
        raise ValueError(f"path must be under {root}: {resolved}")
    return resolved


def sha256(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def key(record: dict[str, Any]) -> tuple[str, int, str, str]:
    return (str(record["source"]), int(record["theorem_id"]),
            str(record["topic"]), str(record["target_key"]))


def select(records: Iterable[dict[str, Any]], *, topic: str | None = None,
           target_key: str | None = None, limit: int | None = None) -> list[dict[str, Any]]:
    selected = [r for r in records if (topic is None or r["topic"] == topic)
                and (target_key is None or r["target_key"] == target_key)]
    if limit is not None and limit < 1:
        raise ValueError("limit must be positive")
    return selected[:limit]


def read_jsonl(path: str | Path) -> list[dict[str, Any]]:
    result = []
    with repo_path(path).open(encoding="utf-8") as stream:
        for number, line in enumerate(stream, 1):
            if line.strip():
                value = json.loads(line)
                if not isinstance(value, dict):
                    raise ValueError(f"expected object at {path}:{number}")
                result.append(value)
    return result


def append_jsonl(path: str | Path, record: dict[str, Any]) -> None:
    destination = repo_path(path)
    destination.parent.mkdir(parents=True, exist_ok=True)
    with destination.open("a", encoding="utf-8") as stream:
        stream.write(json.dumps(record, ensure_ascii=False) + "\n")


def write_jsonl(path: str | Path, records: Iterable[dict[str, Any]]) -> Path:
    destination = repo_path(path)
    destination.parent.mkdir(parents=True, exist_ok=True)
    with destination.open("w", encoding="utf-8") as stream:
        for record in records:
            stream.write(json.dumps(record, ensure_ascii=False) + "\n")
    return destination


def prompt_hash(system: str, user: str) -> str:
    return sha256(system + "\n\n" + user)
