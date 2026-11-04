"""Deterministic, proof-masked retrieval with hard character budgets.

Selected declarations are whole snippets, never byte/character slices of commands.
This is a prompt view, not the Isabelle theory used by the checker.
"""
from __future__ import annotations

from dataclasses import dataclass, replace
from pathlib import Path
from functools import lru_cache
import re
from .common import sha256, repo_path
from ..hundred_theorems_pipeline.hol_syntax import tokens as hol_tokens, phrases
from ..babel_formal_pipeline.isabelle_syntax import tokens as isa_tokens, OUTER_COMMANDS

CONTEXT_VERSION = "most_match_retrieval_v2"
LEGACY_CONTEXT_VERSION = "most_match_retrieval_v1"
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
    origin: str = ""


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


@lru_cache(maxsize=32)
def isabelle_snippets(prefix, *, top_level_only=False):
    items = isa_tokens(prefix)
    starts = [t for t in items if t.kind == "word" and t.text in OUTER_COMMANDS | {"open_bundle"}]
    chunks = []
    for index, token in enumerate(starts):
        end = starts[index + 1].start if index + 1 < len(starts) else len(prefix)
        text = prefix[token.start:end].strip()
        undecorated = re.sub(r"\\<\^marker>(?:\\<open>.*?\\<close>|\u2039.*?\u203a)", "", text, flags=re.S)
        words = isa_tokens(undecorated)
        if token.text in {"lemma", "theorem", "corollary", "proposition"} and (
                len(words) < 2 or words[1].kind != "word" or
                words[1].text in {"assumes", "fixes", "shows", "obtains", "includes"}):
            continue  # An unnamed proposition is not a reusable fact named "open".
        name_token = words[1].text if len(words) > 1 else token.text
        name_match = IDENTIFIER.search(name_token)
        name = name_match[0] if name_match else token.text
        chunks.append(Snippet(name, token.text, token.start, end, text))
    # Preserve the actual active scope headers, including fixed locale parameters
    # and assumptions. Closed scopes are not active assumptions for this target.
    stack, pending, top_level = [], None, []
    for chunk in chunks:
        if len(stack) == 1 and chunk.kind not in {"locale", "class"}:
            # Declarations explicitly inside a locale need its exported signature.
            words = isa_tokens(chunk.text)
            if len(words) < 2 or words[1].text != "(":
                top_level.append(chunk)
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
    return [chunk for chunk in (top_level if top_level_only else chunks) if chunk.kind in allowed], mandatory


def theory_header(text):
    # Limit tokenization to the header: imported proof bodies are not references.
    header = text[:text.find("\nbegin")] if "\nbegin" in text else text
    items = isa_tokens(header)
    at = next((i for i,t in enumerate(items) if t.kind == "word" and t.text == "theory"), None)
    if at is None or at + 1 >= len(items):
        raise ValueError("missing theory header in statement snapshot")
    name = items[at + 1].text.strip('"')
    start = next((i + 1 for i in range(at + 2,len(items)) if items[i].text == "imports"), len(items))
    end = next((i for i in range(start,len(items)) if items[i].text in {"begin","keywords","abbrevs"}),len(items))
    return name, [t.text.strip('"') for t in items[start:end]]


def imported_references(prefix, root):
    """Only transitive imports present in the supplied masked AFP snapshot.

    No target theory, sibling search, external installation or proof file is read.
    Unavailable imports stay unavailable to retrieval; verifier imports are unchanged.
    """
    from ..hundred_theorems_pipeline.masking import mask_isabelle_reference
    target, imports = theory_header(prefix)
    root = repo_path(root)
    seen, parts, sources, missing = {target}, [], [], []
    pending = list(imports)
    while pending:
        name = pending.pop(0)
        # This snapshot contains only unqualified theories of one AFP entry.
        # Never resolve qualified/library paths to a possibly unrelated basename.
        if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", name):
            missing.append(name)
            continue
        if name in seen:
            continue
        seen.add(name)
        path = root / (name + '.thy')
        if not path.is_file():
            missing.append(name)
            continue
        raw = path.read_text(encoding='utf-8')
        declared, parents = theory_header(raw)
        if declared != name:
            raise ValueError("import snapshot/header mismatch: " + str(path))
        masked = mask_isabelle_reference(raw)
        origin = str(path.relative_to(repo_path('.'))).replace('\\','/')
        declarations, _ = isabelle_snippets(masked, top_level_only=True)
        parts.extend(replace(part, origin=origin) for part in declarations)
        sources.append({'theory':name,'path':origin,'raw_sha256':sha256(raw),
                        'masked_sha256':sha256(masked),'imports':parents})
        pending.extend(parents)
    return parts, {'sources':sources,'unresolved_imports':sorted(set(missing))}


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
        named = snippet.name.casefold() in query_ids
        priority = 200 if named and snippet.kind in {"lemma", "theorem", "corollary", "proposition"} else 100 if named else 0
        return priority + overlap + (2 if snippet.kind == "definition" and overlap else 0)
    def rendered(snippet):
        origin = f"; imported from {snippet.origin}" if snippet.origin else ""
        return f"(* {snippet.kind} {snippet.name}; source chars {snippet.start}:{snippet.end}{origin} *)\n{snippet.text}"
    chosen, used = {}, 0
    def add(snippet, required=False):
        nonlocal used
        if (snippet.origin, snippet.start, snippet.end) in chosen:
            return True
        size = len(rendered(snippet)) + (2 if chosen else 0)
        if used + size > budget:
            if required:
                raise ValueError("mandatory target statement/active scope exceeds context budget; increase the cap")
            return False
        chosen[(snippet.origin, snippet.start, snippet.end)] = snippet
        used += size
        return True
    for snippet in mandatory:
        add(snippet, True)
    ranked = sorted(snippets, key=lambda s: (-score(s), -s.start, s.name))
    for snippet in ranked:
        if score(snippet) > 0:
            add(snippet)
    ordered = sorted(chosen.values(), key=lambda s: (s.origin, s.start, s.end))
    text = "\n\n".join(rendered(s) for s in ordered)
    if not text:
        text = "(* No relevant reference declarations fit the context selection. *)"
    if len(text) > budget:
        raise ValueError("retrieved context exceeds its configured budget")
    return text, {"budget_chars": budget, "selected_chars": len(text), "sha256": sha256(text),
                  "candidate_snippets": len(snippets), "selected_snippets": [
                      {"name": s.name, "kind": s.kind, "span": [s.start, s.end], "origin": s.origin,
                       "sha256": sha256(s.text), "score": score(s)} for s in ordered],
                  "omitted_snippets": len(set(snippets) - set(ordered))}


def build_contexts(source, target, isa, *, import_root=None, source_chars=SOURCE_CONTEXT_CHARS, isabelle_chars=ISABELLE_CONTEXT_CHARS):
    source_parts = source_snippets(source.statement_text)
    chosen = [part for part in source_parts if part.name == target.name]
    if len(chosen) != 1:
        raise ValueError("masked source target is missing or ambiguous in reference")
    # Exclude later same-file source facts: they cannot support the original proof.
    source_parts = [part for part in source_parts if part.start <= chosen[0].start]
    hol, hol_meta = retrieve(source_parts, query=target.statement + "\n" + target.proof,
                             budget=source_chars, mandatory=chosen)
    parts, scopes = isabelle_snippets(isa.context_before_target)
    imported, import_meta = imported_references(isa.context_before_target, import_root) if import_root else ([], {})
    reference, isa_meta = retrieve(parts + imported, query=isa.statement + "\n" + target.statement + "\n" + target.proof,
                                   budget=isabelle_chars, mandatory=scopes)
    isa_meta["imported_context"] = import_meta
    return hol, reference, {"version": CONTEXT_VERSION, "unit": "characters",
                            "hol_light": hol_meta, "isabelle": isa_meta,
                            "policy": "earlier_and_imported_masked_statements; active_isabelle_scopes; complete_selected_proof",
                            "verification_context": "full_original_masked_prefix"}


def validate_prompt_context(record):
    metadata = record.get("metadata", {}).get("prompt_context", {})
    if metadata.get("version") not in {CONTEXT_VERSION, LEGACY_CONTEXT_VERSION}:
        raise ValueError("missing/current most-match retrieval metadata; re-extract records")
    for name, field in (("hol_light", "hol_light_reference_context"), ("isabelle", "isabelle_prompt_context")):
        text = record.get(field)
        info = metadata.get(name, {})
        if (not isinstance(text, str) or not text.strip() or len(text) > info.get("budget_chars", 0)
                or len(text) != info.get("selected_chars") or sha256(text) != info.get("sha256")):
            raise ValueError("stale or oversized retrieved context: " + field)
