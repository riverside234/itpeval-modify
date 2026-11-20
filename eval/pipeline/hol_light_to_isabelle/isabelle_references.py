"""Optional Isabelle proof examples for the model's reference context."""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
import json
from pathlib import Path

from eval.pipeline.config import PROOFS_JSON

from .babel_formal_pipeline.common import repo_path, sha256
from .babel_formal_pipeline.isabelle_syntax import inventory_isabelle_declarations, tokens

REFERENCE_FIELD = "isabelle_reference_proofs"
REFERENCE_MODE = "isabelle_reference_proofs_v1"
REFERENCE_DIRECTORY = "isabelle-reference-proofs"
REFERENCE_TITLE = "ISABELLE REFERENCE CONTEXT (HELPER PROOFS WHEN AVAILABLE)"
REFERENCE_NOTE = (
    "Use any supplied Isabelle helper proofs as examples of applicable rules and proof structure. "
    "Check the scope and premises of each fact before applying it to the oracle."
)


def add_argument(parser):
    parser.add_argument("--isabelle-reference-proofs", action="store_true",
                        help="Include available Isabelle helper proofs in the model context.")


def reference_output(path):
    path = Path(path)
    return str(path.parent / REFERENCE_DIRECTORY / path.name)


def has_reference_proofs(record):
    return REFERENCE_FIELD in record.get("metadata", {})


def reference_default(path, records):
    return reference_output(path) if any(has_reference_proofs(row) for row in records) else path


def proof_context(record):
    """Return the opted-in prompt view or let callers use the masked default."""
    if not has_reference_proofs(record):
        return None
    info = record["metadata"][REFERENCE_FIELD]
    text = record.get("isabelle_prompt_context")
    if (not isinstance(info, dict) or info.get("mode") != REFERENCE_MODE
            or not isinstance(text, str) or not text.strip() or sha256(text) != info.get("sha256")):
        raise ValueError("missing or stale Isabelle reference proof context; re-extract records")
    return text


def store_context(record, text, proofs, *, status="matched"):
    """Record hashes of the prompt view and of the selected source proofs."""
    record["isabelle_prompt_context"] = text
    record["context_mode"] = "isabelle_reference_proofs"
    record["metadata"][REFERENCE_FIELD] = {
        "mode": REFERENCE_MODE, "sha256": sha256(text), "status": status,
        "proof_count": len(proofs), "proofs": proofs,
    }


@lru_cache(maxsize=1)
def _aligned_isabelle_proofs(path):
    result = {}
    for row in json.loads(path.read_text(encoding="utf-8")):
        if row.get("prover") != "isabelle" or row.get("source") not in {"babel-formal", "hundred-theorems"}:
            continue
        key = (row["source"], int(row["theorem_id"]))
        if key in result:
            raise ValueError(f"duplicate Isabelle proof variant for {key}")
        result[key] = row
    return result


def aligned_isabelle_proof(topic):
    row = _aligned_isabelle_proofs(PROOFS_JSON).get((topic.source, topic.theorem_id))
    if (row is None or row.get("title") != topic.topic or row.get("tier") != topic.tier
            or not isinstance(row.get("content"), str) or not row["content"].strip()):
        raise ValueError(f"missing or mismatched Isabelle proof variant for {topic.topic}")
    return row["content"], f"eval/data/proofs.json:{topic.source}:{topic.theorem_id}:isabelle"


def paired_proof_file(statement_path):
    stmt = repo_path(statement_path)
    if stmt.suffix != ".thy" or stmt.parent.name != "isabelle" or stmt.parent.parent.name != "stmts":
        raise ValueError("expected an Isabelle statement snapshot")
    return repo_path(stmt.parents[2] / "proofs" / "isabelle" / stmt.name)


def _signature(text):
    return tuple((item.kind, item.text) for item in tokens(text))


@lru_cache(maxsize=64)
def _theory_name(text):
    # The prefix before the first declaration may include sections and comments.
    items = tokens(text)
    for item, following in zip(items, items[1:]):
        if item.kind == "word" and item.text == "theory":
            return following.text.strip('"')
    return None


@dataclass(frozen=True)
class ProofExample:
    name: str
    source: str
    span: tuple[int, int]
    body: str

    @property
    def metadata(self):
        return {"name": self.name, "source": self.source, "span": list(self.span), "sha256": sha256(self.body)}


@dataclass(frozen=True)
class DeclarationProof:
    name: str
    start: int
    signature: tuple
    proof_span: tuple[int, int] | None


def _completed_span(items, start):
    if not items or any(item.kind == "word" and item.text in {"sorry", "oops", "admit"} for item in items):
        return None
    words = [item.text for item in items if item.kind == "word"]
    if not ({"by", "proof", "apply"} & set(words) or items[-1].text == "."):
        return None
    if "by" not in words and "done" not in words and "qed" not in words and items[-1].text != ".":
        return None
    brackets = []
    pairs = {")": "(", "]": "[", "}": "{"}
    for item in items:
        if item.kind != "symbol":
            continue
        if item.text in pairs.values():
            brackets.append(item.text)
        elif item.text in pairs and (not brackets or brackets.pop() != pairs[item.text]):
            return None
    if brackets:
        return None
    depth = 0
    for word in words:
        if word == "proof":
            depth += 1
        elif word == "qed":
            depth -= 1
            if depth < 0:
                return None
    if depth or items[-1].text in {"by", "apply", "using", "unfolding"}:
        return None
    return start + items[0].start, start + items[-1].end


@lru_cache(maxsize=24)
def _proof_index(content):
    declarations = {}
    for declaration in inventory_isabelle_declarations(content):
        start, end = declaration.statement_span
        if declaration.proof_span is None:
            # A standalone '.' or '..' closes some short Isar proofs.
            dots = tokens(content[start:end])
            while dots and dots[-1].text == ".":
                end = start + dots.pop().start
            body_end = declaration.char_end
        else:
            _, body_end = declaration.proof_span
        signature = _signature(content[start:end])
        span = _completed_span(tokens(content[end:body_end]), end)
        proof = DeclarationProof(declaration.name, start, signature, span)
        declarations.setdefault(proof.name, []).append(proof)
    return _theory_name(content), declarations


class ReferenceProofs:
    """Match transcript bodies to the exact earlier declarations in a masked view."""

    def __init__(self, full, source, *, masked_theory, target_name, target_statement=None):
        self.full = full
        self.source = source
        self.target_name = target_name
        self.cutoff = len(full)
        self.status = "matched"
        actual, self.declarations = _proof_index(full)
        if not masked_theory or actual != masked_theory:
            self.status = "theory_mismatch"
        elif target_statement is not None:
            matches = self.declarations.get(target_name, ())
            if len(matches) != 1 or matches[0].signature != _signature(target_statement):
                self.status = "target_boundary_unmatched"
            else:
                self.cutoff = matches[0].start

    def restore(self, masked):
        if self.status != "matched":
            return masked, []
        replacements = []
        for declaration in inventory_isabelle_declarations(masked):
            if declaration.name == self.target_name or declaration.proof_span is None:
                continue
            start, end = declaration.proof_span
            body = tokens(masked[start:end])
            if not body or body[-1].kind != "word" or body[-1].text != "sorry":
                continue
            signature = _signature(masked[slice(*declaration.statement_span)])
            matches = [item for item in self.declarations.get(declaration.name, ())
                       if item.start < self.cutoff and item.signature == signature]
            if len(matches) != 1 or matches[0].proof_span is None or matches[0].proof_span[1] > self.cutoff:
                continue
            span = matches[0].proof_span
            example = ProofExample(declaration.name, self.source, span, self.full[slice(*span)])
            # Preserve the masked declaration and everything following its placeholder.
            replacements.append((start, start + body[-1].end, example))
        pieces, cursor = [], 0
        for start, end, example in replacements:
            indent = "  " if start == 0 or masked[start-1] == "\n" else "\n  "
            pieces.extend([masked[cursor:start], indent, example.body])
            cursor = end
        pieces.append(masked[cursor:])
        return "".join(pieces), [example for _, _, example in replacements]


def attach_aligned_context(record, topic):
    full, source = aligned_isabelle_proof(topic)
    prefix = record["isabelle_context_before_target"]
    references = ReferenceProofs(full, source, masked_theory=_theory_name(prefix),
                                target_name=record["isabelle_target_name"], target_statement=record["isabelle_statement"])
    text, examples = references.restore(prefix)
    store_context(record, text, [example.metadata for example in examples], status=references.status)


def snapshot_references(statement_path, masked, *, target_name, target_statement=None):
    proof_path = paired_proof_file(statement_path)
    if not proof_path.is_file():
        return None
    full = proof_path.read_text(encoding="utf-8")
    return ReferenceProofs(full, proof_path.relative_to(repo_path(".")).as_posix(),
                           masked_theory=_theory_name(masked), target_name=target_name,
                           target_statement=target_statement)
