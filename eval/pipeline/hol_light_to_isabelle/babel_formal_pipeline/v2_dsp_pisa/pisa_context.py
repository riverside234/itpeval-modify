"""Preserve dataset contexts; qualify only explicitly mapped import names."""
from __future__ import annotations
import re
import json
from ..isabelle_syntax import tokens
from ..theory_context import validate_context
from .runtime import DspConfig, PisaFailure

def import_tokens(prefix: str) -> list:
    items = tokens(prefix)
    start = next((i + 1 for i, t in enumerate(items) if t.kind == "word" and t.text == "imports"), None)
    if start is None:
        raise ValueError("missing original theory imports")
    end = next((i for i in range(start, len(items)) if items[i].kind == "word"
                and items[i].text in {"keywords", "abbrevs", "begin"}), len(items))
    imports = [t.text.strip('"') for t in items[start:end]]
    if not imports or any(not re.fullmatch(r"[A-Za-z_0-9./+-]+", name) or ".." in name.split("/")
                          or name.startswith("/") for name in imports):
        raise ValueError("unsupported import; configure a compatible named session dependency")
    return items[start:end]


def imports_of(prefix: str) -> list[str]:
    return [item.text.strip('"') for item in import_tokens(prefix)]


def resolve_imports(source: str, config: DspConfig, *, theory_name: str) -> tuple[str, dict]:
    """Qualify configured imports only; never import a replacement target theory."""
    items = import_tokens(source)
    original = [item.text.strip('"') for item in items]
    resolved = [config.theory_imports.get(name, name) for name in original]
    def basename(name):
        leaf = name.rsplit("/", 1)[-1]
        return (leaf[:-4] if leaf.endswith(".thy") else leaf).rsplit(".", 1)[-1]
    if any(basename(name) == theory_name for name in resolved):
        raise PisaFailure("context_error", "cannot import the selected target theory into PISA")
    sessions = []
    for name in resolved:
        # Dotted theory names identify their owning session. File paths and
        # global names such as Main do not. Isabelle resolves the transitive graph.
        if "/" not in name and "." in name and not name.endswith(".thy"):
            session = name.rsplit(".", 1)[0]
            if session != "HOL" and session not in sessions:
                sessions.append(session)
    # Token offsets preserve comments, original line numbers and all declarations.
    # Stored dataset templates/hashes are never edited.
    for item, before, after in reversed(list(zip(items, original, resolved))):
        if before != after:
            source = source[:item.start] + json.dumps(after) + source[item.end:]
    return source, {"original_imports": original, "resolved_imports": resolved,
                    "session_dependencies": sessions}



def prepare_context(record, config):
    context = validate_context(record)
    prefix, resolution = resolve_imports(context.prefix, config, theory_name=context.theory_name)
    # Background helpers are admitted, as in the experiment's input contract.
    # The selected proof starts after explicitly restoring checked execution.
    begin = next(t for t in tokens(prefix) if t.kind == "word" and t.text == "begin")
    prefix = prefix[:begin.end] + "\ndeclare [[quick_and_dirty = true]]\n" + prefix[begin.end:]
    prefix += "\ndeclare [[quick_and_dirty = false, smt_oracle = false]]\n"
    declaration = context.preamble[len(context.prefix):]
    return context, prefix + declaration, resolution
