"""Explicit file groups; underscore-prefixed library mirrors are not extra targets.

Only HOL Light proofs and both statement variants are opened. Completed Isabelle
proof files are deliberately outside this loader's input contract.
"""
from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from .common import DATASET_ROOT, repo_path, sha256
from ..hundred_theorems_pipeline.hol_syntax import inventory_hol_declarations
from ..hundred_theorems_pipeline.masking import mask_isabelle_reference
from ..babel_formal_pipeline.isabelle_syntax import inventory_isabelle_declarations

TOPICS = {
    "Bumping": ("bumping",),
    "Canonical_Models": ("canonical_models",),
    "Cauchy_Integral_Theorem": ("cauchy_integral_theorem",),
    "Conformal_Mappings": ("conformal_mappings",),
    "Continuous_Extension": ("continuous_extension_1", "continuous_extension_2"),
    "Cross3": ("cross3",),
    "Exact_Sequence": ("exact_sequence",),
    "Fashoda_Theorem": ("fashoda_theorem",),
    "FSigma": ("fsigma",),
    "Great_Picard": ("great_picard",),
    "Improper_Integral": ("improper_integral_1", "improper_integral_2"),
    "Poly_Roots": ("poly_roots",),
    "Polytope": ("polytope",),
    "Product_Groups": ("product_groups",),
    "Skolem_Normal_Form": ("skolem_normal_form",),
    "Vitali_Covering_Theorem": ("vitali_covering_theorem",),
}


@dataclass(frozen=True)
class SourceFile:
    path: str
    statement_path: str
    proof_text: str
    statement_text: str
    proofs: tuple
    statements: tuple


@lru_cache(maxsize=32)
def _declarations(text, masked):
    return tuple(inventory_hol_declarations(text, masked=masked))


def source_file(root, stem):
    proof = repo_path(root) / "proofs" / "hol-light" / (stem + ".ml")
    stmt = repo_path(root) / "stmts" / "hol-light" / (stem + ".ml")
    source, reference = proof.read_text(encoding="utf-8"), stmt.read_text(encoding="utf-8")
    return SourceFile(str(proof), str(stmt), source, reference,
                      _declarations(source, False), _declarations(reference, True))


def load_topic(topic, root=DATASET_ROOT):
    if topic not in TOPICS:
        raise ValueError("unknown most-match topic: " + topic)
    target_path = repo_path(root) / "stmts" / "isabelle" / (topic + ".thy")
    raw = target_path.read_text(encoding="utf-8")
    template = mask_isabelle_reference(raw)
    sources, seen = [], set()
    for stem in TOPICS[topic]:
        source = source_file(root, stem)
        identity = (sha256(source.proof_text), sha256(source.statement_text))
        if identity not in seen:
            sources.append(source)
            seen.add(identity)
    return {"topic": topic, "theorem_id": list(TOPICS).index(topic) + 1,
            "sources": sources, "template": template, "raw_template": raw,
            "target_path": str(target_path),
            "targets": inventory_isabelle_declarations(template, topic=topic)}


def topics(topic=None):
    if topic is not None and topic not in TOPICS:
        raise ValueError("unknown most-match topic: " + topic)
    return [topic] if topic else list(TOPICS)
