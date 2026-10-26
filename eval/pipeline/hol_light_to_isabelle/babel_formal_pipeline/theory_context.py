"""Validate the masked oracle and retain the target's original Isabelle scopes."""

from __future__ import annotations

import re
from dataclasses import dataclass

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.common import fingerprint, sha256
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.prompt import normalize_visible_content
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.sanitize_isabelle import sanitize_declaration, sanitize_target
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.isabelle_syntax import inventory_isabelle_declarations


from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.isabelle_syntax import Token, tokens


FORBIDDEN = {
    "sorry", "oops", "admit", "axiomatization", "axioms", "oracle", "theory",
    "locale", "theorem", "lemma", "corollary", "proposition", "definition",
    "ML", "ML_file", "ML_val", "ML_prf", "SML_file", "setup", "local_setup",
    "method_setup", "attribute_setup", "declaration", "tactic", "raw_tactic",
    "end", "context", "notepad", "declare", "interpretation", "experiment",
    "fun", "primrec", "datatype", "record", "class", "instance", "instantiation",
    "syntax", "translations", "notation", "unbundle", "bundle", "include",
    "external_file", "text", "section", "subsection",
}


def normalize_body(proof: str, *, allow_hammer: bool = False) -> str:
    body = normalize_visible_content(proof)
    items = tokens(body)
    words = [item.text for item in items if item.kind == "word"]
    banned = FORBIDDEN | {"normalhammer", "Skip_Proof", "skip_proof", "cheat"}
    if not allow_hammer:
        banned = banned | {"sledgehammer"}
    bad = set(words) & banned
    if bad:
        raise ValueError("proof contains admission or forbidden command: " + ", ".join(sorted(bad)))
    if not items or items[0].text not in {"by", "proof"}:
        raise ValueError("proof body must start with by or proof")
    if items[0].text == "proof" and items[-1].text != "qed":
        raise ValueError("structured proof must end with qed")
    return body


@dataclass(frozen=True)
class TargetContext:
    theory_name: str
    template: str
    prefix: str
    statement: str
    proof_prefix: str
    proof_span: tuple[int, int]
    depth: int
    prior_names: tuple[str, ...]

    @property
    def preamble(self) -> str:
        return self.template[:self.proof_span[0]]

    @property
    def metadata(self) -> dict:
        return {
            "draft_context_policy": "original_masked_prefix",
            "context_sha256": sha256(self.prefix),
            "statement_sha256": sha256(self.statement),
            "template_sha256": sha256(self.template),
            "background_policy": "earlier_masked_helpers_admitted",
            "admitted_background_names": list(self.prior_names),
            "admitted_background_count": len(self.prior_names),
        }

    def theory(self, proof: str, *, full: bool = False, allow_hammer: bool = False) -> str:
        body = normalize_body(proof, allow_hammer=allow_hammer)
        start, end = self.proof_span
        suffix = self.template[end:] if full else "\n" + "end\n" * self.depth
        return self.preamble + body + suffix


def validate_context(record: dict) -> TargetContext:
    template = record.get("isabelle_theory_template")
    if not isinstance(template, str):
        raise ValueError("missing Isabelle theory template")
    name = record.get("isabelle_target_name")
    target = sanitize_target(template, name, topic=record.get("topic", ""))
    if list(target.proof_span) != record.get("isabelle_target_proof_span"):
        raise ValueError("stale or invalid Isabelle target proof span")
    for field, actual in (
        ("isabelle_statement", target.statement),
        ("isabelle_context_before_target", target.context_before_target),
        ("isabelle_proof_prefix", target.proof_prefix),
    ):
        if record.get(field, "") != actual:
            raise ValueError("stored target does not match masked template: " + field)
    expected = record.get("metadata", {}).get("isabelle_stmt_sha256")
    if expected and expected != sha256(template):
        raise ValueError("masked Isabelle template hash mismatch")
    items = tokens(target.context_before_target)
    theory_index = next((i for i, item in enumerate(items) if item.kind == "word" and item.text == "theory"), -1)
    if theory_index < 0 or theory_index + 1 >= len(items):
        raise ValueError("missing Isabelle theory declaration")
    theory_name = items[theory_index + 1].text.strip('"')
    if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", theory_name):
        raise ValueError("unsupported Isabelle theory name")
    depth = 0
    for item in items:
        if item.kind == "word" and item.text in {"begin", "end"}:
            depth += 1 if item.text == "begin" else -1
            if depth < 0:
                raise ValueError("unbalanced Isabelle context scopes")
    if depth < 1:
        raise ValueError("target is outside an open Isabelle theory")
    prior = inventory_isabelle_declarations(target.context_before_target)
    for declaration in prior:
        # Declaration spans can also include subsequent primrec/notation commands.
        # Validate the helper's placeholder without treating those commands as proof.
        sanitize_declaration(target.context_before_target, declaration)
    return TargetContext(
        theory_name, template, target.context_before_target, target.statement,
        target.proof_prefix, target.proof_span, depth, tuple(item.name for item in prior))


def input_metadata(record: dict) -> dict:
    draft = record.get("draft")
    if not isinstance(draft, str) or not draft.strip() or record.get("draft_error"):
        raise ValueError("a successful saved mathematical Draft is required")
    context = validate_context(record)
    result = {**context.metadata, "draft_sha256": sha256(draft)}
    for name in ("draft_sha256", "context_sha256", "statement_sha256", "template_sha256"):
        if record.get(name) and record[name] != result[name]:
            raise ValueError("stale saved input: " + name)
    result["input_fingerprint"] = fingerprint({
        **result, "source_metadata": record.get("metadata"),
    })
    return result
