"""Deterministic, proof-masked retrieval with hard character budgets.

Selected declarations are whole snippets, never byte/character slices of commands.
This is a prompt view, not the Isabelle theory used by the checker.
"""
from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
import re
from .common import sha256
from ..hundred_theorems_pipeline.hol_syntax import tokens as hol_tokens, phrases
from ..babel_formal_pipeline.isabelle_syntax import tokens as isa_tokens, OUTER_COMMANDS

CONTEXT_VERSION = "most_match_retrieval_v1"
SOURCE_CONTEXT_CHARS = 16000
ISABELLE_CONTEXT_CHARS = 8000
IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z_0-9']*")
STOP = set("let in and or if then else lambda forall exists lemma theorem assumes shows fixes for where sorry by proof qed real nat bool set True False".split())


@dataclass(frozen=True)
class Snippet:
    name: str
    kind: str
    start: int
    end: int
    text: str


@lru_cache(maxsize=32768)
def identifiers(text):
    return frozenset(word.casefold() for word in IDENTIFIER.findall(text) if len(word) > 2 and word not in STOP)


@lru_cache(maxsize=24)
def source_snippets(text):
    result = []
    for phrase in phrases(hol_tokens(text)):
        if len(phrase) < 5 or phrase[0].text != "let" or phrase[1].kind != "word" or phrase[2].text != "=":
            continue
        rhs = phrase[3]
        if rhs.kind == "term" and len(phrase) == 5:
            kind = "statement"
        elif rhs.text in {"new_definition", "new_recursive_definition", "define"} and any(t.kind == "term" for t in phrase):
            kind = "definition"
        else:
            continue  # Tactic programs, theorem-producing code and local lets are not reference facts.
        if any(t.kind == "word" and t.text == "prove" for t in phrase):
            continue
        a, b = phrase[0].start, phrase[-1].end
        result.append(Snippet(phrase[1].text, kind, a, b, text[a:b]))
    return tuple(result)


def isabelle_snippets(prefix):
    items = isa_tokens(prefix)
    starts = [t for t in items if t.kind == "word" and t.text in OUTER_COMMANDS | {"open_bundle"}]
    chunks = []
    for index, token in enumerate(starts):
        end = starts[index + 1].start if index + 1 < len(starts) else len(prefix)
        text = prefix[token.start:end].strip()
        undecorated = re.sub(r"\\<\^marker>(?:\\<open>.*?\\<close>|\u2039.*?\u203a)", "", text, flags=re.S)
        words = isa_tokens(undecorated)
        name_token = words[1].text if len(words) > 1 else token.text
        name_match = IDENTIFIER.search(name_token)
        name = name_match[0] if name_match else token.text
        chunks.append(Snippet(name, token.text, token.start, end, text))
    # Preserve the actual active scope headers, including fixed locale parameters
    # and assumptions. Closed scopes are not active assumptions for this target.
    stack, pending = [], None
    for chunk in chunks:
        if chunk.kind in {"theory", "context", "locale", "class", "instantiation", "overloading", "bundle", "open_bundle"}:
            pending = chunk
        elif chunk.kind == "begin":
            stack.append(pending or chunk)
            pending = None
        elif chunk.kind == "end":
            if stack:
                stack.pop()
            pending = None
    mandatory = list(dict.fromkeys(stack))
    allowed = {"lemma", "theorem", "corollary", "proposition", "definition", "abbreviation",
               "fun", "primrec", "datatype", "type_synonym", "notation", "lemmas", "unbundle",
               "include", "includes", "named_theorems", "locale", "class"}
    return [chunk for chunk in chunks if chunk.kind in allowed], mandatory


def retrieve(snippets, *, query, budget, mandatory=()):
    if isinstance(budget, bool) or not isinstance(budget, int) or budget < 256:
        raise ValueError("context budgets must be integer character counts >= 256")
    query_ids = identifiers(query)
    # One deterministic dependency expansion: directly named helpers contribute
    # identifiers from their statements, improving definition retrieval.
    expanded = set(query_ids)
    for snippet in snippets:
        if snippet.name.casefold() in query_ids:
            expanded.update(identifiers(snippet.text))
    def score(snippet):
        overlap = len(identifiers(snippet.text) & expanded)
        return (100 if snippet.name.casefold() in query_ids else 0) + overlap + (2 if snippet.kind == "definition" and overlap else 0)
    def rendered(snippet):
        return f"(* {snippet.kind} {snippet.name}; source chars {snippet.start}:{snippet.end} *)\n{snippet.text}"
    chosen, used = {}, 0
    def add(snippet, required=False):
        nonlocal used
        if (snippet.start, snippet.end) in chosen:
            return True
        size = len(rendered(snippet)) + (2 if chosen else 0)
        if used + size > budget:
            if required:
                raise ValueError("mandatory target statement/active scope exceeds context budget; increase the cap")
            return False
        chosen[(snippet.start, snippet.end)] = snippet
        used += size
        return True
    for snippet in mandatory:
        add(snippet, True)
    ranked = sorted(snippets, key=lambda s: (-score(s), -s.start, s.name))
    for snippet in ranked:
        if score(snippet) > 0:
            add(snippet)
    ordered = sorted(chosen.values(), key=lambda s: (s.start, s.end))
    text = "\n\n".join(rendered(s) for s in ordered)
    if not text:
        text = "(* No relevant reference declarations fit the context selection. *)"
    if len(text) > budget:
        raise ValueError("retrieved context exceeds its configured budget")
    return text, {"budget_chars": budget, "selected_chars": len(text), "sha256": sha256(text),
                  "candidate_snippets": len(snippets), "selected_snippets": [
                      {"name": s.name, "kind": s.kind, "span": [s.start, s.end],
                       "sha256": sha256(s.text), "score": score(s)} for s in ordered],
                  "omitted_snippets": len(set(snippets) - set(ordered))}


def build_contexts(source, target, isa, *, source_chars=SOURCE_CONTEXT_CHARS, isabelle_chars=ISABELLE_CONTEXT_CHARS):
    source_parts = source_snippets(source.statement_text)
    chosen = [part for part in source_parts if part.name == target.name]
    if len(chosen) != 1:
        raise ValueError("masked source target is missing or ambiguous in reference")
    # Exclude later same-file source facts: they cannot support the original proof.
    source_parts = [part for part in source_parts if part.start <= chosen[0].start]
    hol, hol_meta = retrieve(source_parts, query=target.statement + "\n" + target.proof,
                             budget=source_chars, mandatory=chosen)
    parts, scopes = isabelle_snippets(isa.context_before_target)
    reference, isa_meta = retrieve(parts, query=isa.statement + "\n" + target.statement + "\n" + target.proof,
                                   budget=isabelle_chars, mandatory=scopes)
    return hol, reference, {"version": CONTEXT_VERSION, "unit": "characters",
                            "hol_light": hol_meta, "isabelle": isa_meta,
                            "policy": "earlier_statements_and_definitions; active_isabelle_scopes; complete_selected_proof",
                            "verification_context": "full_original_masked_prefix"}


def validate_prompt_context(record):
    metadata = record.get("metadata", {}).get("prompt_context", {})
    if metadata.get("version") != CONTEXT_VERSION:
        raise ValueError("missing/current most-match retrieval metadata; re-extract records")
    for name, field in (("hol_light", "hol_light_reference_context"), ("isabelle", "isabelle_prompt_context")):
        text = record.get(field)
        info = metadata.get(name, {})
        if (not isinstance(text, str) or not text.strip() or len(text) > info.get("budget_chars", 0)
                or len(text) != info.get("selected_chars") or sha256(text) != info.get("sha256")):
            raise ValueError("stale or oversized retrieved context: " + field)
