from __future__ import annotations

import json
from dataclasses import dataclass
from functools import lru_cache

from eval.pipeline.config import PROOFS_JSON, STMTS_JSON
from eval.pipeline.hol_light_to_isabelle.common import sha256


@dataclass(frozen=True)
class AlignedTopic:
    theorem_id: int
    topic: str
    tier: str
    hol_light_proof_content: str
    hol_light_stmt_content: str
    isabelle_stmt_content: str
    hol_light_proof_sha256: str
    hol_light_stmt_sha256: str
    isabelle_stmt_sha256: str


@lru_cache(maxsize=2)
def _index(path: str, provers: tuple[str, ...]) -> dict[tuple[int, str], dict]:
    # Retain only the requested prover variants in the aligned input index.
    with open(path, encoding="utf-8") as stream:
        records = json.load(stream)
    result = {}
    for record in records:
        if record.get("source") != "babel-formal" or record.get("prover") not in provers:
            continue
        record_key = (int(record["theorem_id"]), record["prover"])
        if record_key in result:
            raise ValueError(f"duplicate Babel record {record_key}")
        result[record_key] = record
    return result


def list_topics() -> list[tuple[int, str]]:
    proofs = _index(str(PROOFS_JSON), ("hol-light",))
    return sorted((theorem_id, record["title"])
                  for (theorem_id, _), record in proofs.items())


def load_topic(theorem_id: int) -> AlignedTopic:
    proof = _index(str(PROOFS_JSON), ("hol-light",))[(theorem_id, "hol-light")]
    statements = _index(str(STMTS_JSON), ("hol-light", "isabelle"))
    hol_stmt = statements[(theorem_id, "hol-light")]
    isa_stmt = statements[(theorem_id, "isabelle")]
    if len({r["title"] for r in (proof, hol_stmt, isa_stmt)}) != 1:
        raise ValueError(f"title mismatch at theorem_id={theorem_id}")
    if len({r["tier"] for r in (proof, hol_stmt, isa_stmt)}) != 1:
        raise ValueError(f"tier mismatch at theorem_id={theorem_id}")
    if any(not r.get("content") for r in (proof, hol_stmt, isa_stmt)):
        raise ValueError(f"empty content at theorem_id={theorem_id}")
    return AlignedTopic(
        theorem_id=theorem_id, topic=proof["title"], tier=proof["tier"],
        hol_light_proof_content=proof["content"],
        hol_light_stmt_content=hol_stmt["content"],
        isabelle_stmt_content=isa_stmt["content"],
        hol_light_proof_sha256=sha256(proof["content"]),
        hol_light_stmt_sha256=sha256(hol_stmt["content"]),
        isabelle_stmt_sha256=sha256(isa_stmt["content"]),
    )


def iter_topics(*, topic: str | None = None, theorem_id: int | None = None):
    for candidate_id, candidate_topic in list_topics():
        if topic is not None and topic != candidate_topic:
            continue
        if theorem_id is not None and theorem_id != candidate_id:
            continue
        yield load_topic(candidate_id)
