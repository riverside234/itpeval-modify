from __future__ import annotations

import json
from pathlib import Path
from typing import Callable, Iterable, TypeVar

T = TypeVar("T", bound=dict)


def load_jsonl(path: Path) -> list[dict]:
    records: list[dict] = []
    if not path.exists():
        return records
    # Invalid JSONL is treated as a data error instead of being silently skipped
    with path.open("r", encoding="utf-8", errors="replace") as f:
        for lineno, line in enumerate(f, 1):
            line = line.strip()
            if not line:
                continue
            try:
                records.append(json.loads(line))
            except json.JSONDecodeError as e:
                raise ValueError(f"{path}:{lineno}: invalid JSONL: {e}") from e
    return records


def load_checkpoint(path: Path, key_fn: Callable[[dict], str]) -> dict[str, dict]:
    # Later checkpoint rows replace earlier rows with the same key
    return {key_fn(r): r for r in load_jsonl(path)}


def write_jsonl_atomic(path: Path, records: Iterable[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp_path = path.with_suffix(path.suffix + ".tmp")
    # Write the final ordered file only after all rows are ready
    with tmp_path.open("w", encoding="utf-8") as f:
        for record in records:
            f.write(json.dumps(record, ensure_ascii=False) + "\n")
    tmp_path.replace(path)
