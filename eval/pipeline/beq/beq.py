from __future__ import annotations

import re
from dataclasses import dataclass

from eval.pipeline.verify import verify
from itpeval.itp import run_itp


@dataclass
class BEqResult:
    equivalent: bool = False
    forward_ok: bool = False
    backward_ok: bool = False
    forward_tactic: str = ""
    backward_tactic: str = ""
    forward_ms: int = 0
    backward_ms: int = 0
    forward_error: str = ""
    backward_error: str = ""
    extraction_error: str = ""


def _lean4_extract_header_and_theorem(content: str) -> tuple[str, str]:
    """Split Lean 4 content into (header, theorem_block).

    Header = imports/opens/set_option before the first theorem/lemma.
    Theorem_block = everything from 'theorem'/'lemma' onwards.
    """
    lines = content.split("\n")
    for i, line in enumerate(lines):
        if re.match(r'(theorem|lemma)\s', line.strip()):
            header = "\n".join(lines[:i]).rstrip()
            theorem_block = "\n".join(lines[i:]).rstrip()
            return header, theorem_block

    raise ValueError("no theorem/lemma found in Lean 4 content")


def _lean4_rename_theorem(theorem_block: str, new_name: str) -> str:
    """Rename the theorem/lemma in a Lean 4 theorem block."""
    return re.sub(
        r'^(theorem|lemma)\s+\S+',
        rf'\1 {new_name}',
        theorem_block,
        count=1,
    )


def _lean4_replace_proof(theorem_block: str, tactic_body: str) -> str:
    """Replace the proof body with the given tactic body."""
    result = re.sub(
        r':=\s*(?:by\b.*)?\bsorry\s*$',
        f":= by\n{tactic_body}",
        theorem_block,
        flags=re.DOTALL,
    )
    if result == theorem_block:
        raise ValueError("could not replace proof in Lean 4 theorem")
    return result


LEAN4_EXACT_TACTIC = "  exact?"

LEAN4_NORMAL_CANDIDATES = [
    ("exact", "  exact stmt_assumed"),
    ("apply", "  apply stmt_assumed"),
    ("rw", "  rw [stmt_assumed]"),
    ("rw_rev", "  rw [← stmt_assumed]"),
    ("intro", "  intro; exact stmt_assumed"),
    ("intros", "  intros; exact stmt_assumed"),
    ("constructor", "  constructor <;> exact stmt_assumed"),
    ("ext", "  ext; exact stmt_assumed"),
    ("have", "  have h := stmt_assumed; exact h"),
    ("cases'", "  cases' stmt_assumed with h; exact h"),
    ("use", "  use stmt_assumed"),
]


def _build_beq_lean4_attempt(
    header: str, assumed_thm: str, goal_thm: str, tactic_body: str,
) -> str:
    """Build a Lean 4 file for one BEq proof attempt."""
    assumed = _lean4_rename_theorem(assumed_thm, "stmt_assumed")
    goal_base = _lean4_rename_theorem(goal_thm, "beq_goal")
    goal = _lean4_replace_proof(goal_base, tactic_body)
    return "\n".join([header, "", assumed, "", goal, ""])


def _rocq_extract_header_and_type(content: str) -> tuple[str, str]:
    """Extract (header, proposition_type) from Rocq content."""
    m = re.search(r'(Theorem|Lemma)\s+[\w\']+', content)
    if not m:
        raise ValueError("no Theorem/Lemma found in Rocq content")

    header = content[:m.start()].rstrip()
    after_name = content[m.end():]

    depth = 0
    for i, ch in enumerate(after_name):
        if ch in "({":
            depth += 1
        elif ch in ")}":
            depth -= 1
        elif ch == ":" and depth == 0:
            type_start = i + 1
            break
    else:
        raise ValueError("no ':' found in Rocq theorem")

    rest = after_name[type_start:]

    end_m = re.search(r'\n\s*(?:Proof\.|Admitted\.)', rest)
    type_text = rest[:end_m.start()] if end_m else rest
    type_text = type_text.rstrip().rstrip(".")
    prop = type_text.strip()
    if not prop:
        raise ValueError("empty proposition in Rocq content")
    return header, prop


ROCQ_TACTICS = [
    ("exact", "exact stmt_assumed."),
    ("auto", "auto using stmt_assumed."),
    ("eauto", "eauto using stmt_assumed."),
    ("tauto", "tauto."),
    ("intuition", "intuition; try exact stmt_assumed."),
    ("firstorder", "firstorder using stmt_assumed."),
    ("congruence", "congruence."),
    ("lia", "lia."),
    ("lra", "lra."),
    ("nra", "nra."),
    ("ring", "ring."),
    ("field_simplify", "field_simplify; try ring."),
    ("fourier", "fourier."),
    ("psatz", "psatz Z 3."),
]


def _merge_rocq_headers(ref_header: str, gen_header: str) -> str:
    """Merge Rocq import headers so both types are in scope."""
    seen = set()
    lines = []
    for header in (ref_header, gen_header):
        for line in header.split("\n"):
            stripped = line.strip()
            if stripped and stripped not in seen:
                seen.add(stripped)
                lines.append(stripped)
    return "\n".join(lines)


def _build_beq_rocq(
    header: str, type_assumed: str, type_goal: str, tactic_body: str,
) -> str:
    parts = [header, ""] if header.strip() else []
    parts.append(f"Axiom stmt_assumed : {type_assumed}.")
    parts.append("")
    parts.append(f"Theorem beq_goal : {type_goal}.")
    parts.append("Proof.")
    parts.append(f"  {tactic_body}")
    parts.append("Qed.")
    return "\n".join(parts) + "\n"


def _isabelle_extract_imports_and_theorem(content: str) -> tuple[str, str]:
    """Extract (imports_clause, theorem_block) from Isabelle content.

    imports_clause: the value after 'imports' in the theory header (e.g. 'Complex_Main').
    theorem_block: the full theorem/lemma block inside begin...end.
    """
    m = re.search(r'imports\s+(.*?)(?:\s+begin|$)', content, re.DOTALL)
    imports = m.group(1).strip() if m else "Main"

    m = re.search(
        r'((?:theorem|lemma)\s+\w+.*?)(?=\n\s*(?:theorem|lemma|end)\b)',
        content,
        re.DOTALL,
    )
    if not m:
        m = re.search(r'((?:theorem|lemma)\s+\w+.*?)(?:\s*end\s*$)', content, re.DOTALL)
    if not m:
        raise ValueError("no theorem/lemma block found in Isabelle content")

    thm_block = m.group(1).rstrip()
    return imports, thm_block


def _isabelle_rename_theorem(theorem_block: str, new_name: str) -> str:
    return re.sub(
        r'^(theorem|lemma)\s+\w+',
        rf'\1 {new_name}',
        theorem_block,
        count=1,
    )


def _isabelle_replace_proof_with_cascade(theorem_block: str) -> str:
    """Replace 'by sorry' or 'oops' with a tactic cascade using stmt_assumed."""
    has_assumes = bool(re.search(r'\bassumes\b', theorem_block))
    using_line = "  using assms\n" if has_assumes else ""
    cascade = f"""\
{using_line}  by (rule stmt_assumed
     | auto simp add: stmt_assumed
     | simp add: stmt_assumed
     | blast
     | force
     | fastforce
     | metis stmt_assumed
     | meson stmt_assumed
     | smt (verit) stmt_assumed
     | smt (z3) stmt_assumed
     | arith
     | linarith
     | presburger
     | normalization
     | argo
     | algebra
     | (insert stmt_assumed, auto)
     | (insert stmt_assumed, force)
     | (insert stmt_assumed, blast))"""

    result = re.sub(
        r'\b(?:by\s+sorry|oops|sorry)\s*$',
        cascade,
        theorem_block,
        flags=re.DOTALL,
    )
    if result == theorem_block:
        raise ValueError("could not replace proof in Isabelle theorem")
    return result


def _build_beq_isabelle(
    imports: str, assumed_thm: str, goal_thm: str,
    theory_name: str = "BEq_Check",
) -> str:
    assumed = _isabelle_rename_theorem(assumed_thm, "stmt_assumed")
    goal = _isabelle_rename_theorem(goal_thm, "beq_goal")
    goal = _isabelle_replace_proof_with_cascade(goal)
    return f"""theory {theory_name}
  imports {imports}
begin

{assumed}

{goal}

end
"""


def _hol_light_extract_header_and_type(content: str) -> tuple[str, str]:
    """Extract (header, proposition) from HOL Light content."""
    lines = content.split("\n")
    header_lines = []
    rest_start = 0

    for i, line in enumerate(lines):
        stripped = line.strip()
        if re.match(r'let\s+\S+\s*=', stripped):
            rest_start = i
            break
        if stripped.startswith(("needs ", "loads ")):
            header_lines.append(line)
            rest_start = i + 1

    header = "\n".join(header_lines).rstrip()
    rest = "\n".join(lines[rest_start:])

    for pattern in [
        r'prove\s*\(\s*`(.*?)`',
        r'new_axiom\s*`(.*?)`',
        r'let\s+\S+\s*=\s*`(.*?)`',
    ]:
        m = re.search(pattern, rest, re.DOTALL)
        if m:
            return header, m.group(1).strip()

    raise ValueError("could not extract proposition from HOL Light content")


def _build_beq_hol_light(
    header: str, type_assumed: str, type_goal: str,
) -> str:
    parts = []
    if header.strip():
        parts.append(header)
        parts.append("")
    parts.append(f"let stmt_assumed = new_axiom `{type_assumed}`;;")
    parts.append("")
    parts.append(f"let beq_goal = prove(`{type_goal}`,")
    parts.append("  ACCEPT_TAC stmt_assumed")
    parts.append("  ORELSE (ASM_MESON_TAC [stmt_assumed])")
    parts.append("  ORELSE (ASM_SIMP_TAC [stmt_assumed])")
    parts.append("  ORELSE (REWRITE_TAC [stmt_assumed] THEN ARITH_TAC)")
    parts.append("  ORELSE (ASM_REWRITE_TAC [stmt_assumed])")
    parts.append("  ORELSE (SIMP_TAC [stmt_assumed])")
    parts.append("  ORELSE (MESON_TAC [stmt_assumed])")
    parts.append("  ORELSE (REWRITE_TAC [stmt_assumed] THEN REAL_ARITH_TAC)")
    parts.append("  ORELSE (REWRITE_TAC [stmt_assumed] THEN INT_ARITH_TAC)")
    parts.append("  ORELSE (REWRITE_TAC [stmt_assumed] THEN NORM_TAC)")
    parts.append("  ORELSE (ASM_REWRITE_TAC [stmt_assumed] THEN ARITH_TAC)")
    parts.append("  ORELSE (MATCH_ACCEPT_TAC stmt_assumed)")
    parts.append("  ORELSE (NUMBER_TAC)")
    parts.append("  ORELSE (ITAUT_TAC)")
    parts.append(");;")
    return "\n".join(parts) + "\n"


def _timeout_for(prover: str) -> int:
    return {"lean4": 120, "rocq": 30, "isabelle": 300, "hol-light": 360}.get(prover, 120)


def _exact_suggests_stmt_assumed(output: str) -> bool:
    return any(
        "Try this: exact" in line and "stmt_assumed" in line
        for line in output.splitlines()
    )


def _check_direction_lean4(
    ref_header: str, assumed_thm: str, goal_thm: str,
) -> tuple[bool, str, int, str]:
    total_ms = 0
    last_error = ""

    try:
        code = _build_beq_lean4_attempt(ref_header, assumed_thm, goal_thm, LEAN4_EXACT_TACTIC)
    except ValueError as e:
        return False, "", 0, str(e)

    rr = run_itp(prover="lean4", code=code, timeout_s=_timeout_for("lean4"))
    total_ms += rr.duration_ms
    output = (rr.stdout or "") + "\n" + (rr.stderr or "")
    if rr.ok and _exact_suggests_stmt_assumed(output):
        return True, "exact", total_ms, ""
    if rr.ok:
        last_error = "exact? succeeded without referencing stmt_assumed"
    else:
        last_error = output.strip()

    for tactic_name, tactic_body in LEAN4_NORMAL_CANDIDATES:
        try:
            code = _build_beq_lean4_attempt(ref_header, assumed_thm, goal_thm, tactic_body)
        except ValueError as e:
            return False, "", total_ms, str(e)

        rr = run_itp(prover="lean4", code=code, timeout_s=_timeout_for("lean4"))
        total_ms += rr.duration_ms
        output = (rr.stdout or "") + "\n" + (rr.stderr or "")
        if rr.ok:
            return True, f"normal:{tactic_name}", total_ms, ""
        last_error = output.strip()

    return False, "", total_ms, last_error


def _check_direction_rocq(
    header: str, type_assumed: str, type_goal: str,
) -> tuple[bool, str, int, str]:
    total_ms = 0
    last_error = ""
    for tactic_name, tactic_body in ROCQ_TACTICS:
        code = _build_beq_rocq(header, type_assumed, type_goal, tactic_body)
        vr = verify("rocq", code, timeout_s=_timeout_for("rocq"))
        total_ms += vr.duration_ms
        if vr.ok:
            return True, tactic_name, total_ms, ""
        last_error = vr.error
    return False, "", total_ms, last_error


def _check_direction_isabelle(
    imports: str, assumed_thm: str, goal_thm: str,
) -> tuple[bool, str, int, str]:
    code = _build_beq_isabelle(imports, assumed_thm, goal_thm)
    vr = verify("isabelle", code, timeout_s=_timeout_for("isabelle"))
    return vr.ok, ("auto_cascade" if vr.ok else ""), vr.duration_ms, vr.error


def _check_direction_hol_light(
    header: str, type_assumed: str, type_goal: str,
) -> tuple[bool, str, int, str]:
    code = _build_beq_hol_light(header, type_assumed, type_goal)
    vr = verify("hol-light", code, timeout_s=_timeout_for("hol-light"))
    return vr.ok, ("orelse_cascade" if vr.ok else ""), vr.duration_ms, vr.error


def beq_check(
    tgt_prover: str,
    generated_content: str,
    reference_content: str,
) -> BEqResult:
    """Run BEq between generated and reference statements in tgt_prover."""
    result = BEqResult()

    if tgt_prover == "lean4":
        return _beq_lean4(generated_content, reference_content)
    elif tgt_prover == "rocq":
        return _beq_rocq(generated_content, reference_content)
    elif tgt_prover == "isabelle":
        return _beq_isabelle(generated_content, reference_content)
    elif tgt_prover == "hol-light":
        return _beq_hol_light(generated_content, reference_content)
    else:
        result.extraction_error = f"unsupported prover: {tgt_prover}"
        return result


def _beq_lean4(gen_content: str, ref_content: str) -> BEqResult:
    result = BEqResult()
    try:
        ref_header, ref_thm = _lean4_extract_header_and_theorem(ref_content)
        _, gen_thm = _lean4_extract_header_and_theorem(gen_content)
    except (ValueError, IndexError) as e:
        result.extraction_error = str(e)
        return result

    if "maxHeartbeats" not in ref_header:
        ref_header = "set_option maxHeartbeats 400000\n" + ref_header

    fwd_ok, fwd_t, fwd_ms, fwd_e = _check_direction_lean4(ref_header, gen_thm, ref_thm)
    result.forward_ok, result.forward_tactic = fwd_ok, fwd_t
    result.forward_ms, result.forward_error = fwd_ms, fwd_e

    bwd_ok, bwd_t, bwd_ms, bwd_e = _check_direction_lean4(ref_header, ref_thm, gen_thm)
    result.backward_ok, result.backward_tactic = bwd_ok, bwd_t
    result.backward_ms, result.backward_error = bwd_ms, bwd_e

    result.equivalent = fwd_ok and bwd_ok
    return result


def beq_check_lean4_batch(
    items: list[tuple[str, str, str]],
    timeout_s: int = 600,
) -> list[BEqResult]:
    """Reliable Lean 4 BEq for many pairs.

    items: list of (record_id, generated_content, reference_content).
    Returns: list of BEqResult in same order.

    This intentionally checks each proof candidate independently, matching the
    original BEq acceptance rule more closely than the old combined-file parser:
    accept only successful Lean runs, and require exact? suggestions to mention
    stmt_assumed. The timeout_s argument is kept for the runner API.
    """
    results: list[BEqResult] = []
    for _record_id, gen_content, ref_content in items:
        results.append(_beq_lean4(gen_content, ref_content))

    return results


def _beq_rocq(gen_content: str, ref_content: str) -> BEqResult:
    result = BEqResult()
    try:
        ref_header, ref_type = _rocq_extract_header_and_type(ref_content)
        gen_header, gen_type = _rocq_extract_header_and_type(gen_content)
    except (ValueError, IndexError) as e:
        result.extraction_error = str(e)
        return result

    header = _merge_rocq_headers(ref_header, gen_header)

    fwd_ok, fwd_t, fwd_ms, fwd_e = _check_direction_rocq(header, gen_type, ref_type)
    result.forward_ok, result.forward_tactic = fwd_ok, fwd_t
    result.forward_ms, result.forward_error = fwd_ms, fwd_e

    bwd_ok, bwd_t, bwd_ms, bwd_e = _check_direction_rocq(header, ref_type, gen_type)
    result.backward_ok, result.backward_tactic = bwd_ok, bwd_t
    result.backward_ms, result.backward_error = bwd_ms, bwd_e

    result.equivalent = fwd_ok and bwd_ok
    return result


def _beq_isabelle(gen_content: str, ref_content: str) -> BEqResult:
    result = BEqResult()
    try:
        ref_imports, ref_thm = _isabelle_extract_imports_and_theorem(ref_content)
        _, gen_thm = _isabelle_extract_imports_and_theorem(gen_content)
    except (ValueError, IndexError) as e:
        result.extraction_error = str(e)
        return result

    fwd_ok, fwd_t, fwd_ms, fwd_e = _check_direction_isabelle(ref_imports, gen_thm, ref_thm)
    result.forward_ok, result.forward_tactic = fwd_ok, fwd_t
    result.forward_ms, result.forward_error = fwd_ms, fwd_e

    bwd_ok, bwd_t, bwd_ms, bwd_e = _check_direction_isabelle(ref_imports, ref_thm, gen_thm)
    result.backward_ok, result.backward_tactic = bwd_ok, bwd_t
    result.backward_ms, result.backward_error = bwd_ms, bwd_e

    result.equivalent = fwd_ok and bwd_ok
    return result


def _beq_hol_light(gen_content: str, ref_content: str) -> BEqResult:
    result = BEqResult()
    try:
        ref_header, ref_type = _hol_light_extract_header_and_type(ref_content)
        _, gen_type = _hol_light_extract_header_and_type(gen_content)
    except (ValueError, IndexError) as e:
        result.extraction_error = str(e)
        return result

    fwd_ok, fwd_t, fwd_ms, fwd_e = _check_direction_hol_light(ref_header, gen_type, ref_type)
    result.forward_ok, result.forward_tactic = fwd_ok, fwd_t
    result.forward_ms, result.forward_error = fwd_ms, fwd_e

    bwd_ok, bwd_t, bwd_ms, bwd_e = _check_direction_hol_light(ref_header, ref_type, gen_type)
    result.backward_ok, result.backward_tactic = bwd_ok, bwd_t
    result.backward_ms, result.backward_error = bwd_ms, bwd_e

    result.equivalent = fwd_ok and bwd_ok
    return result
