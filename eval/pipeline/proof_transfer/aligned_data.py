from __future__ import annotations

import hashlib
import json
from dataclasses import asdict, dataclass
from functools import lru_cache
from pathlib import Path
from typing import Any, Iterable

from eval.pipeline.config import PROOFS_JSON, REPO_ROOT, STMTS_JSON


BABEL_FORMAL = "babel-formal"
ISABELLE = "isabelle"
LEAN4 = "lean4"
LAB_REPO_ROOT = "/data/not_backed_up/yxu209/ITPEval"
PROOF_TRANSFER_DIR = Path(__file__).resolve().parent


@dataclass(frozen=True)
class AlignedBabelTopic:
    theorem_id: int
    topic: str
    tier: str
    isabelle_proof_content: str
    isabelle_stmt_content: str
    lean4_stmt_content: str
    isabelle_proof_sha256: str
    isabelle_stmt_sha256: str
    lean4_stmt_sha256: str

    def to_metadata_dict(self) -> dict[str, Any]:
        data = asdict(self)
        for key in (
            "isabelle_proof_content",
            "isabelle_stmt_content",
            "lean4_stmt_content",
        ):
            data.pop(key, None)
        return data


def sha256_text(content: str) -> str:
    return hashlib.sha256(content.encode("utf-8")).hexdigest()


def resolved_repo_root() -> Path:
    return REPO_ROOT.resolve(strict=False)


def _is_under(path: Path, root: Path) -> bool:
    try:
        path.relative_to(root)
    except ValueError:
        return False
    return True


def validate_repo_layout(expected_root: str | Path | None = None) -> dict[str, str]:
    root = resolved_repo_root()
    if expected_root is not None:
        expected = Path(expected_root).expanduser().resolve(strict=False)
        if root != expected:
            raise RuntimeError(
                f"expected repo root {expected}, but eval.pipeline.config resolved {root}"
            )

    required_paths = {
        "repo_root": REPO_ROOT,
        "stmts_json": STMTS_JSON,
        "proofs_json": PROOFS_JSON,
        "proof_transfer_dir": PROOF_TRANSFER_DIR,
        "babel_targets_json": PROOF_TRANSFER_DIR / "manifests" / "babel_targets.json",
        "extract_isabelle_py": PROOF_TRANSFER_DIR / "extract_isabelle.py",
        "sanitize_lean_py": PROOF_TRANSFER_DIR / "sanitize_lean.py",
    }
    resolved_paths: dict[str, str] = {}
    for name, path in required_paths.items():
        resolved = path.resolve(strict=False)
        if not _is_under(resolved, root):
            raise RuntimeError(f"{name} resolves outside repo root: {resolved}")
        if not path.exists():
            raise FileNotFoundError(f"missing required {name}: {resolved}")
        resolved_paths[name] = str(resolved)
    return resolved_paths


@lru_cache(maxsize=None)
def _load_records(path: str) -> tuple[dict[str, Any], ...]:
    return tuple(json.loads(Path(path).read_text(encoding="utf-8")))


def load_stmt_records() -> tuple[dict[str, Any], ...]:
    return _load_records(str(STMTS_JSON))


def load_proof_records() -> tuple[dict[str, Any], ...]:
    return _load_records(str(PROOFS_JSON))


def _record_index(records: Iterable[dict[str, Any]]) -> dict[tuple[str, int, str], dict[str, Any]]:
    index: dict[tuple[str, int, str], dict[str, Any]] = {}
    for record in records:
        if not record.get("content"):
            continue
        key = (record["source"], int(record["theorem_id"]), record["prover"])
        index[key] = record
    return index


@lru_cache(maxsize=1)
def _proof_index() -> dict[tuple[str, int, str], dict[str, Any]]:
    return _record_index(load_proof_records())


@lru_cache(maxsize=1)
def _stmt_index() -> dict[tuple[str, int, str], dict[str, Any]]:
    return _record_index(load_stmt_records())


def list_babel_topics() -> list[tuple[int, str]]:
    topics = [
        (int(record["theorem_id"]), record["title"])
        for record in load_proof_records()
        if record["source"] == BABEL_FORMAL and record["prover"] == ISABELLE
    ]
    return sorted(topics)


def _get_record(
    index: dict[tuple[str, int, str], dict[str, Any]],
    *,
    source: str,
    theorem_id: int,
    prover: str,
) -> dict[str, Any]:
    key = (source, int(theorem_id), prover)
    try:
        return index[key]
    except KeyError as exc:
        raise KeyError(f"missing record for source={source!r}, theorem_id={theorem_id}, prover={prover!r}") from exc


def load_babel_topic(theorem_id: int) -> AlignedBabelTopic:
    isabelle_proof = _get_record(
        _proof_index(),
        source=BABEL_FORMAL,
        theorem_id=theorem_id,
        prover=ISABELLE,
    )
    isabelle_stmt = _get_record(
        _stmt_index(),
        source=BABEL_FORMAL,
        theorem_id=theorem_id,
        prover=ISABELLE,
    )
    lean4_stmt = _get_record(
        _stmt_index(),
        source=BABEL_FORMAL,
        theorem_id=theorem_id,
        prover=LEAN4,
    )

    titles = {
        isabelle_proof["title"],
        isabelle_stmt["title"],
        lean4_stmt["title"],
    }
    if len(titles) != 1:
        raise ValueError(f"title mismatch for Babel theorem_id={theorem_id}: {sorted(titles)}")

    return AlignedBabelTopic(
        theorem_id=int(theorem_id),
        topic=isabelle_proof["title"],
        tier=isabelle_proof["tier"],
        isabelle_proof_content=isabelle_proof["content"],
        isabelle_stmt_content=isabelle_stmt["content"],
        lean4_stmt_content=lean4_stmt["content"],
        isabelle_proof_sha256=sha256_text(isabelle_proof["content"]),
        isabelle_stmt_sha256=sha256_text(isabelle_stmt["content"]),
        lean4_stmt_sha256=sha256_text(lean4_stmt["content"]),
    )


def load_babel_topic_by_name(topic: str) -> AlignedBabelTopic:
    for theorem_id, candidate_topic in list_babel_topics():
        if candidate_topic == topic:
            return load_babel_topic(theorem_id)
    raise KeyError(f"unknown Babel Formal topic: {topic!r}")


def iter_babel_topics(
    *,
    theorem_ids: Iterable[int] | None = None,
    topics: Iterable[str] | None = None,
) -> Iterable[AlignedBabelTopic]:
    allowed_ids = {int(theorem_id) for theorem_id in theorem_ids} if theorem_ids else None
    allowed_topics = set(topics) if topics else None

    for theorem_id, topic in list_babel_topics():
        if allowed_ids is not None and theorem_id not in allowed_ids:
            continue
        if allowed_topics is not None and topic not in allowed_topics:
            continue
        yield load_babel_topic(theorem_id)
