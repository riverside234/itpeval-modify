"""OCaml phrase inventory; local let-bindings cannot become theorem targets."""

from __future__ import annotations

from dataclasses import dataclass
import re

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.inventory import HolDeclaration


@dataclass(frozen=True)
class Token:
    text: str
    start: int
    end: int
    kind: str = "symbol"


WORD = re.compile(r"[A-Za-z_][A-Za-z_0-9']*")


def tokens(content: str) -> list[Token]:
    result = []
    i = 0
    while i < len(content):
        start = i
        if content[i].isspace():
            i += 1
        elif content.startswith("(*", i):
            depth = 1
            i += 2
            while i < len(content) and depth:
                if content.startswith("(*", i):
                    depth += 1
                    i += 2
                elif content.startswith("*)", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ValueError("unterminated OCaml comment")
        elif content[i] in {'"', chr(96)}:
            delim = content[i]
            i += 1
            while i < len(content) and content[i] != delim:
                i += 2 if delim == '"' and content[i] == "\\" else 1
            if i >= len(content):
                raise ValueError("unterminated OCaml string/HOL quotation")
            i += 1
            result.append(Token(content[start:i], start, i, "term" if delim == chr(96) else "string"))
        elif content.startswith(";;", i):
            i += 2
            result.append(Token(";;", start, i))
        else:
            match = WORD.match(content, i)
            if match:
                i = match.end()
                result.append(Token(match[0], start, i, "word"))
            else:
                i += 1
                result.append(Token(content[start:i], start, i))
    return result


def prove_call(items: list[Token], index: int) -> tuple[int, int, int]:
    if index + 3 >= len(items) or items[index+1].text != "(" or items[index+2].kind != "term" or items[index+3].text != ",":
        raise ValueError(f"unsupported prove call at offset {items[index].start}")
    depth = 1
    cursor = index + 2
    while cursor + 1 < len(items) and depth:
        cursor += 1
        depth += (items[cursor].text == "(") - (items[cursor].text == ")")
    if depth:
        raise ValueError(f"unterminated prove call at offset {items[index].start}")
    return index+2, index+3, cursor


def phrases(items: list[Token]):
    start = 0
    for index, item in enumerate(items):
        if item.text == ";;":
            yield items[start:index+1]
            start = index+1
    if start < len(items):
        raise ValueError("unterminated top-level OCaml phrase")


def inventory_hol_declarations(content: str, *, masked: bool) -> list[HolDeclaration]:
    result = []
    for phrase in phrases(tokens(content)):
        if len(phrase) < 5 or phrase[0].text != "let" or phrase[1].kind != "word" or phrase[2].text != "=":
            continue
        rhs = phrase[3]
        term = comma = close = None
        if masked:
            if rhs.kind != "term" or len(phrase) != 5:
                continue
            term = rhs
        elif rhs.text == "prove":
            ti, ci, ei = prove_call(phrase, 3)
            # "let th = prove(...) in add_to_diff_net th" is local, not an export.
            if ei != len(phrase)-2:
                continue
            term, comma, close = phrase[ti], phrase[ci], phrase[ei]
        else:
            continue
        statement = term.text[1:-1].strip()
        proof = content[comma.end:close.start].strip() if comma else None
        if not statement or (not masked and not proof):
            raise ValueError(f"empty theorem {phrase[1].text}")
        start, end = phrase[0].start, phrase[-1].end
        result.append(HolDeclaration(
            phrase[1].text, statement, proof, (start,end),
            (term.start+1,term.end-1), (comma.end,close.start) if comma else None,
            content.count("\n",0,start)+1, content.count("\n",0,end)+1,
            content[start:end]))
    return result


def mask_reference(content: str) -> str:
    """Remove residual proof-producing phrases, including tuple/local bindings.

    A literal proposition is retained when available. OCaml proof generators
    such as SET_RULE tm = prove(tm, ...) have no literal statement and are
    omitted from the reference rather than exposing their tactic programs.
    """
    replacements = []
    for number, phrase in enumerate(phrases(tokens(content))):
        proof_indices = [i for i,item in enumerate(phrase)
                         if item.kind == "word" and item.text == "prove"]
        if not proof_indices:
            continue
        statements = []
        for index in proof_indices:
            cursor = index + 1
            while cursor < len(phrase) and phrase[cursor].text == ")":
                cursor += 1
            if cursor+1 < len(phrase) and phrase[cursor].text == "(" and phrase[cursor+1].kind == "term":
                statements.append(phrase[cursor+1].text)
        reference = "\\n".join(
            f"let V2_MASKED_HELPER_{number}_{i} = {statement};;"
            for i,statement in enumerate(statements))
        if not reference:
            reference = "(* OCaml proof-producing helper omitted. *)"
        replacements.append((phrase[0].start,phrase[-1].end,reference))
    for start,end,replacement in reversed(replacements):
        content = content[:start]+replacement+content[end:]
    if any(item.kind == "word" and item.text == "prove" for item in tokens(content)):
        raise ValueError("HOL reference still contains an executable prove call")
    return content
