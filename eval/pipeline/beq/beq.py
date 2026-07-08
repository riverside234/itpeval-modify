from __future__ import annotations

import re
from dataclasses import dataclass

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
            # Imports and options are reused for both BEq directions
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


def _timeout_for(prover: str) -> int:
    return {"lean4": 120}.get(prover, 120)


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

    # exact? is accepted only when its suggestion depends on stmt_assumed
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
        # Each tactic is checked in a fresh Lean file to avoid cross-attempt state
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


def beq_check(
    tgt_prover: str,
    generated_content: str,
    reference_content: str,
) -> BEqResult:
    """Run BEq between generated and reference statements in tgt_prover."""
    result = BEqResult()

    if tgt_prover == "lean4":
        return _beq_lean4(generated_content, reference_content)

    result.extraction_error = f"BEq is reported for lean4 targets, got: {tgt_prover}"
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
        # BEq attempts may need more search budget than the reference statement file
        ref_header = "set_option maxHeartbeats 400000\n" + ref_header

    fwd_ok, fwd_t, fwd_ms, fwd_e = _check_direction_lean4(ref_header, gen_thm, ref_thm)
    result.forward_ok, result.forward_tactic = fwd_ok, fwd_t
    result.forward_ms, result.forward_error = fwd_ms, fwd_e

    bwd_ok, bwd_t, bwd_ms, bwd_e = _check_direction_lean4(ref_header, ref_thm, gen_thm)
    result.backward_ok, result.backward_tactic = bwd_ok, bwd_t
    result.backward_ms, result.backward_error = bwd_ms, bwd_e

    result.equivalent = fwd_ok and bwd_ok
    return result
