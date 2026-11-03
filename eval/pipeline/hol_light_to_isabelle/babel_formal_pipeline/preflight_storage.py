"""Bounded, Git-friendly preflight reports; complete artifacts stay local."""
from __future__ import annotations

import json
import time
from pathlib import Path

from .common import repo_path

MIB = 1024 * 1024
MAX_FILE_BYTES = 32 * MIB
MAX_DETAIL_BYTES = 48 * 1024
MAX_LOG_BYTES = 16 * 1024
MAX_LOG_FILES = 1024
REPORT_FILES = {"report.json", "summary.md", "checks.jsonl", "metadata.json",
                "logs.jsonl", "unavailable_contexts.json"}


def encode(value):
    return (json.dumps(value, ensure_ascii=False, separators=(",", ":")) + "\n").encode("utf-8")


def excerpt(text, limit=2048):
    if len(text) <= limit:
        return text
    half = max(1, (limit - 80) // 2)
    return text[:half] + f"\n... [truncated; original {len(text)} characters; full text retained locally] ...\n" + text[-half:]


def compact(value, limit=MAX_DETAIL_BYTES):
    """Keep small payloads intact; retain structured fields and explicit truncation."""
    if len(encode(value)) <= limit:
        return value
    def shrink(item, width):
        if isinstance(item, str):
            return excerpt(item, width)
        if isinstance(item, dict):
            return {k: shrink(v, width) for k, v in item.items()}
        if isinstance(item, (list, tuple)):
            if len(item) > 32:
                return [*(shrink(v, width) for v in item[:16]),
                        {"_omitted_items": len(item) - 32},
                        *(shrink(v, width) for v in item[-16:])]
            return [shrink(v, width) for v in item]
        return item
    for width in (4096, 1024, 256):
        result = shrink(value, width)
        if len(encode(result)) <= limit:
            return result
    # Pathological payloads still cannot create an unpushable report file.
    return {"_truncated": True, "preview": excerpt(encode(value).decode("utf-8"), limit // 8),
            "full_payload": "See local_artifacts: checks.full.jsonl for new runs, details/ for legacy runs"}


def write_json(path, value):
    write_bytes(path, encode(value))


def replace_file(source, destination):
    # Windows indexers/previewers can briefly deny atomic replacement. Keep the
    # previous report intact, retry only those Windows errors, then propagate.
    for attempt in range(7):
        try:
            source.replace(destination)
            return
        except PermissionError as exc:
            if getattr(exc, "winerror", None) not in {5, 32, 33} or attempt == 6:
                raise
            time.sleep(0.02 * 2**attempt)


def write_bytes(path, data):
    if len(data) > MAX_FILE_BYTES:
        raise ValueError(f"Report size limit exceeded: {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_bytes(data)
    replace_file(temporary, path)


def append_jsonl(path, value, *, bounded=True):
    data = encode(value)
    if bounded and (path.stat().st_size if path.exists() else 0) + len(data) > MAX_FILE_BYTES:
        raise ValueError(f"Report size limit exceeded: {path}")
    with path.open("ab") as stream:
        stream.write(data)


class ReportStorage:
    def __init__(self, path: Path, *, work_path=None):
        self.path = repo_path(path)
        self.work_path = repo_path(work_path) if work_path else repo_path(
            Path("itpeval/.runs/preflight") / self.path.parent.name / self.path.name)
        if self.work_path == self.path or self.work_path.is_relative_to(self.path):
            raise ValueError("Runtime artifacts must be outside the publishable report directory")
        self.work_path.mkdir(parents=True, exist_ok=True)
        (self.path / "checks.jsonl").touch(exist_ok=True)

    def record(self, row, payload):
        append_jsonl(self.work_path / "checks.full.jsonl", {**row, "payload": payload}, bounded=False)
        append_jsonl(self.path / "checks.jsonl", {**row, "payload": compact(payload)})

    def finish(self):
        metadata = {}
        for name in ("config.json", "backend.json", "dependencies.json", "release_sources.json"):
            source = self.work_path / name
            if source.is_file():
                metadata[name] = compact(json.loads(source.read_text(encoding="utf-8")), 256 * 1024)
        stats = {"included": 0, "omitted": 0, "truncated": 0, "read_errors": 0,
                 "max_excerpt_bytes": MAX_LOG_BYTES, "max_files": MAX_LOG_FILES}
        target = self.path / "logs.jsonl"
        temporary = target.with_name("logs.jsonl.tmp")
        with temporary.open("wb") as stream:
            for source in sorted(self.work_path.rglob("*")):
                if source.is_symlink() or not source.is_file():
                    continue
                if not (source.suffix == ".log" or source.name.endswith(".processes.json")):
                    continue
                if stats["included"] >= MAX_LOG_FILES:
                    stats["omitted"] += 1
                    continue
                row = {"path": source.relative_to(self.work_path).as_posix()}
                try:
                    size = source.stat().st_size
                    with source.open("rb") as raw:
                        head = raw.read(MAX_LOG_BYTES // 2)
                        if size > MAX_LOG_BYTES:
                            raw.seek(-MAX_LOG_BYTES // 2, 2)
                            text = head + b"\n... [truncated; full log retained locally] ...\n" + raw.read(MAX_LOG_BYTES // 2)
                        else:
                            text = head + raw.read(MAX_LOG_BYTES // 2)
                    row.update(original_bytes=size, truncated=size > MAX_LOG_BYTES,
                               text=text.decode("utf-8", errors="replace"))
                    stats["truncated"] += int(row["truncated"])
                except OSError as exc:
                    row["read_error"] = str(exc)
                    stats["read_errors"] += 1
                data = encode(row)
                if stream.tell() + len(data) > MAX_FILE_BYTES:
                    stats["omitted"] += 1
                    continue
                stream.write(data)
                stats["included"] += 1
        replace_file(temporary, target)
        metadata["log_export"] = stats
        metadata["local_artifacts"] = str(self.work_path)
        write_json(self.path / "metadata.json", metadata)
        return stats
