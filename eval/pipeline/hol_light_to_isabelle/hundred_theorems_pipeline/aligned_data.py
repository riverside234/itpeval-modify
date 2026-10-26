"""Load aligned inputs without loading completed Isabelle proofs."""

from __future__ import annotations

import json
from functools import lru_cache
from pathlib import Path

from eval.pipeline.config import PROOFS_JSON, STMTS_JSON
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.aligned_data import AlignedTopic
from .common import SOURCE, sha256
from .hol_syntax import mask_reference
from .masking import mask_isabelle_reference


@lru_cache(maxsize=2)
def _index(path: str, provers: tuple[str, ...]) -> dict:
    result = {}
    for record in json.loads(Path(path).read_text(encoding="utf-8")):
        if record.get("source") != SOURCE or record.get("prover") not in provers:
            continue
        identity = (int(record["theorem_id"]), record["prover"])
        if identity in result:
            raise ValueError(f"duplicate Hundred Theorems record {identity}")
        result[identity] = record
    return result


def list_topics() -> list[tuple[int, str]]:
    return sorted((tid,record["title"])
                  for (tid,_),record in _index(str(PROOFS_JSON),("hol-light",)).items())


def raw_inputs(theorem_id: int) -> tuple[dict,dict,dict]:
    proof = _index(str(PROOFS_JSON),("hol-light",))[(theorem_id,"hol-light")]
    statements = _index(str(STMTS_JSON),("hol-light","isabelle"))
    try:
        source, target = statements[(theorem_id,"hol-light")], statements[(theorem_id,"isabelle")]
    except KeyError as exc:
        raise ValueError(f"missing aligned statement variant at theorem_id={theorem_id}") from exc
    if len({item["title"] for item in (proof,source,target)}) != 1:
        raise ValueError("aligned file title mismatch")
    if len({item["tier"] for item in (proof,source,target)}) != 1:
        raise ValueError("aligned tier mismatch")
    if any(not isinstance(item.get("content"),str) or not item["content"].strip()
           for item in (proof,source,target)):
        raise ValueError("empty aligned file")
    return proof,source,target


@lru_cache(maxsize=64)
def load_topic(theorem_id: int) -> AlignedTopic:
    proof,source,target = raw_inputs(theorem_id)
    source_context = mask_reference(source["content"])
    target_context = mask_isabelle_reference(target["content"])
    return AlignedTopic(
        theorem_id, proof["title"], proof["tier"], proof["content"],
        source_context, target_context, sha256(proof["content"]),
        sha256(source_context), sha256(target_context), source=SOURCE)


def iter_topics(*, topic: str | None = None, theorem_id: int | None = None):
    for tid,title in list_topics():
        if (topic is None or topic == title) and (theorem_id is None or theorem_id == tid):
            yield load_topic(tid)
