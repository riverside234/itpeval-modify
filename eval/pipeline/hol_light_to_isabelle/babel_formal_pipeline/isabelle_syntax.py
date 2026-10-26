"""Lexical Isabelle inventory shared by the two dataset pipelines."""

from __future__ import annotations

import re
from dataclasses import dataclass
from functools import lru_cache
from eval.pipeline.proof_transfer.inventory import Declaration

WORD = re.compile(r"[A-Za-z_][A-Za-z_0-9'.]*")

@dataclass(frozen=True)
class Token:
    text: str
    start: int
    end: int
    kind: str = "word"


def tokens(text: str) -> list[Token]:
    """Ignore nested comments; preserve quoted terms/cartouches as single tokens."""
    result = []
    i = 0
    while i < len(text):
        start = i
        if text[i].isspace():
            i += 1
        elif text.startswith("(*", i):
            depth = 1
            i += 2
            while i < len(text) and depth:
                if text.startswith("(*", i):
                    depth += 1
                    i += 2
                elif text.startswith("*)", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ValueError("unterminated Isabelle comment")
        elif text[i] == '"':
            i += 1
            while i < len(text) and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            if i >= len(text):
                raise ValueError("unterminated Isabelle string")
            i += 1
            result.append(Token(text[start:i], start, i, "string"))
        elif text.startswith("\\<open>", i) or text[i] == "\u2039":
            opening, closing = ("\\<open>", "\\<close>") if text[i] == "\\" else ("\u2039", "\u203a")
            depth = 1
            i += len(opening)
            while i < len(text) and depth:
                if text.startswith(opening, i):
                    depth += 1
                    i += len(opening)
                elif text.startswith(closing, i):
                    depth -= 1
                    i += len(closing)
                else:
                    i += 1
            if depth:
                raise ValueError("unterminated Isabelle cartouche")
            result.append(Token(text[start:i], start, i, "cartouche"))
        else:
            word = WORD.match(text, i)
            if word:
                i += len(word[0])
                result.append(Token(word[0], start, i))
            else:
                i += 1
                result.append(Token(text[start:i], start, i, "symbol"))
    return result


# Outer commands delimit a theorem body. Terms, comments, and ML cartouches
# are opaque, so words inside them cannot create false declarations.
OUTER_COMMANDS = set("""
private qualified theory end begin lemma theorem corollary proposition schematic_goal
definition abbreviation notation no_notation syntax no_syntax translations
no_translations type_synonym typedecl datatype datatype_new codatatype
fun function primrec primcorec inductive coinductive inductive_set
coinductive_set record locale context class subclass instantiation instance
interpretation sublocale overloading experiment notepad bundle unbundle
include includes declare lemmas named_theorems hide_const hide_fact hide_type
hide_class setup local_setup ML ML_file ML_val ML_prf SML_file method_setup
attribute_setup simproc_setup declaration axiomatization axioms consts
constdefs defs specification typedef quotient_type lift_definition
code_printing code_identifier code_reserved export_code value values
term thm typ print_statement find_theorems text text_raw txt section
subsection subsubsection chapter paragraph subparagraph
termination partial_function global_interpretation declare_file external_file
nonterminal syntax_declaration oracle
""".split())
PROOF_COMMANDS = {"by", "proof", "apply", "sorry", "using", "unfolding"}


def line_start(text: str, offset: int) -> int:
    start = text.rfind("\n", 0, offset) + 1
    return start if not text[start:offset].strip() else offset


@lru_cache(maxsize=64)
def inventory_isabelle_declarations(content: str, *, topic: str = "") -> list[Declaration]:
    items = tokens(content)
    declarations = []
    for index, item in enumerate(items):
        if item.kind != "word" or item.text not in {"lemma", "theorem", "corollary", "proposition"}:
            continue
        beginning = content.rfind("\n", 0, item.start) + 1
        leading = content[beginning:item.start]
        if leading.strip() and not re.fullmatch(r"\s*(?:(?:private|qualified)\s+)+", leading):
            continue
        cursor = index + 1
        if cursor < len(items) and items[cursor].text == "(":
            while cursor < len(items) and items[cursor].text != ")":
                cursor += 1
            cursor += 1
        if cursor >= len(items) or items[cursor].kind not in {"word", "string"}:
            continue
        name = items[cursor].text.strip('"')
        cursor += 1
        if cursor < len(items) and items[cursor].text == "[":
            depth = 1
            cursor += 1
            while cursor < len(items) and depth:
                depth += (items[cursor].text == "[") - (items[cursor].text == "]")
                cursor += 1
        if cursor >= len(items) or items[cursor].text != ":":
            continue
        boundary = next((other.start for other in items[cursor + 1:]
                         if other.kind == "word" and other.text in OUTER_COMMANDS), len(content))
        proof = next((other for other in items[cursor + 1:]
                      if other.start < boundary and other.kind == "word"
                      and other.text in PROOF_COMMANDS), None)
        start = beginning
        end = len(content[:boundary].rstrip())
        proof_start = line_start(content, proof.start) if proof else end
        declarations.append(Declaration(
            prover="isabelle", topic=topic, kind=item.text, name=name,
            line_start=content.count("\n", 0, start) + 1,
            line_end=content.count("\n", 0, max(start, end-1)) + 1,
            char_start=start, char_end=end,
            statement_span=(start, proof_start),
            proof_span=(proof_start, end) if proof else None,
            declaration_span=(start, end), text=content[start:end]))
    return declarations
