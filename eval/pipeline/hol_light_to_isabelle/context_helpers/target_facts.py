"""Rank candidates from masked Isabelle snapshots and resolve a bounded shortlist."""

from dataclasses import replace
from pathlib import Path
import re

from ..babel_formal_pipeline.theory_context import validate_context
from ..babel_formal_pipeline.v2_dsp.native_search import FACT_NAME, forbidden_fact_names
from ..most_match_pipeline.common import repo_path, sha256
from ..most_match_pipeline.context import IDENTIFIER, identifiers, imported_references, isabelle_snippets
from .selection import Selection


FACT_KINDS = {"lemma", "theorem", "corollary", "proposition", "lemmas"}
VOCABULARY_KINDS = {"definition", "abbreviation", "fun", "primrec", "datatype", "type_synonym",
                    "inductive", "inductive_set", "function", "record"}


def candidates(record, hints, helper_symbols, config, *, dataset_root):
    context = validate_context(record)
    local, scopes = isabelle_snippets(context.prefix, active_only=True)
    snapshot = repo_path(dataset_root).parent
    imported, import_info = imported_references(
        context.prefix, snapshot / "afp" / "stmts" / "isabelle",
        extra_roots=(snapshot / "hol" / "stmts" / "isabelle",),
        max_files=config.max_import_files, max_chars=config.max_import_chars)
    blocked = set(forbidden_fact_names(context))
    direct = identifiers(record["hol_light_proof"])
    main = identifiers(context.statement + "\n" + record["hol_light_statement"])
    hint_names = {}
    for hint in hints:
        hint_names.setdefault(hint.casefold(), hint)
    query = main | direct | helper_symbols | hint_names.keys()
    ranked = []
    for item in [*local, *imported]:
        if item.name in blocked:
            continue
        name = item.name.casefold()
        named = hint_names.get(name)
        overlap = len(identifiers(item.text) & query)
        score = 200 * (name in direct) + 100 * (named is not None) + overlap
        if score <= 0:
            continue
        requested = item.name
        if item.origin:
            requested = Path(item.origin).stem + "." + item.name
        ranked.append((score, item, requested, named))
    def ranking(entry):
        score, item, _, named = entry
        # Large facts accrue overlap by mentioning more symbols. For explicit
        # names prefer compact signatures within the same evidence tier.
        tier = 2 * (item.name.casefold() in direct) + (named is not None)
        return (-tier, len(item.text) if tier else 0, -score, item.origin, -item.start, item.name)
    ranked.sort(key=ranking)
    # Qualified imported lookup avoids resolving a short name to an unrelated
    # local fact. Deduplicate requests, keeping the highest-ranked provenance.
    shortlist = {}
    for score, item, requested, named in ranked:
        if item.kind in FACT_KINDS and FACT_NAME.fullmatch(requested):
            shortlist.setdefault(requested, (item, named, score))
            if len(shortlist) >= config.max_fact_candidates:
                break
    return ranked, scopes, shortlist, import_info


def select_target(ranked, scopes, shortlist, imports, *, budget, inspection=None):
    selection = Selection(budget, scopes)
    inspected = {fact["requested"]: fact for fact in inspection["facts"]} if inspection is not None else {}
    vocabulary = [item for _, item, _, _ in ranked if item.kind in VOCABULARY_KINDS]
    added_names = set()
    evidence, visible, requested_vocabulary = [], [], {}
    for requested, (item, source_name, score) in shortlist.items():
        fact = inspected.get(requested)
        status = fact["status"] if fact is not None else "snapshot_only"
        detail = {"requested": requested, "availability": status, "scope": "",
                  "source_name_match": source_name, "ranking_score": score,
                  "origin": item.origin, "span": [item.start, item.end],
                  "snapshot_sha256": sha256(item.text), "selection": "unavailable"}
        evidence.append(detail)
        if status not in {"resolved", "snapshot_only"}:
            continue
        name = fact["name"] if status == "resolved" else requested
        if name in added_names:
            detail["selection"] = "duplicate"
            continue
        if status == "resolved":
            signature = "\n".join(f"  ({i}) {prop}" for i, prop in enumerate(fact["propositions"], 1))
            scope = fact["scope"]
            text = f"(* Isabelle fact resolved before the oracle ({scope} scope). *)\n{name}:\n{signature}"
            detail.update(name=name, scope=scope, signature_sha256=sha256(signature),
                          propositions=len(fact["propositions"]))
            candidate = replace(item, name=name, kind="signature", text=text)
        else:
            candidate = item
        if source_name:
            candidate = replace(candidate, text=f"(* Candidate name match to HOL Light {source_name}. *)\n"
                                                 + candidate.text)
        # Isabelle symbol escapes (e.g. \<And>) are syntax, not references to
        # same-spelled constructors in a snapshot.
        needed = set(IDENTIFIER.findall(re.sub(r"\\<[^>]+>", " ", candidate.text)))
        required = [entry for entry in vocabulary if entry.name in needed
                    and (entry.origin or not item.origin and entry.start < item.start)]
        visible.append(candidate)
        if selection.add([*required, candidate]) or selection.add_optional(candidate):
            requested_vocabulary[requested] = required
            added_names.add(name)
            detail["selection"] = "selected"
        else:
            detail["selection"] = "over_budget"
    optional = [item for _, item, _, _ in ranked if item.kind not in FACT_KINDS]
    for item in optional:
        selection.add_optional(item)
    for detail in evidence:
        required = requested_vocabulary.get(detail["requested"], ())
        if required:
            detail["omitted_vocabulary"] = [entry.name for entry in required
                                            if selection.span_key(entry) not in selection.items]
    context, info = selection.finish([*visible, *optional])
    info["imported_context"] = imports
    info["unshortlisted_facts"] = sum(item.kind in FACT_KINDS for _, item, _, _ in ranked) - len(shortlist)
    info["fact_availability"] = "native_before_oracle" if inspection is not None else "snapshot_only"
    return context, info, evidence
