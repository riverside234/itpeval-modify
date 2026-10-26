"""Repair incomplete proof masking in the aligned Hundred Theorems statements."""

from __future__ import annotations

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.isabelle_syntax import (
    OUTER_COMMANDS, tokens,
)


def mask_isabelle_reference(content: str) -> str:
    items = tokens(content)
    replacements = []
    covered = -1
    for index, item in enumerate(items):
        is_proof = ((item.kind == "word" and item.text in {"by", "proof", "apply"})
                    or (item.kind == "symbol" and item.text == "."))
        if item.start < covered or not is_proof:
            continue
        # All quoted terms/cartouches/comments are opaque to tokens().
        # Strip the entire proof region, including nested proof commands.
        boundary = next((other.start for other in items[index+1:]
                         if other.kind == "word" and other.text in OUTER_COMMANDS), len(content))
        # A proof's local "next" or "qed" is not an outer declaration.
        end = len(content[:boundary].rstrip())
        if end <= item.start:
            raise ValueError("empty Isabelle proof masking span")
        replacements.append((item.start,end,"\n  sorry\n"))
        covered = end
    for start,end,replacement in reversed(replacements):
        content = content[:start]+replacement+content[end:]
    remaining = {item.text for item in tokens(content) if item.kind == "word"} & {"by","proof","apply","oops"}
    if remaining:
        raise ValueError("unmasked Isabelle proof commands: "+", ".join(sorted(remaining)))
    return content
