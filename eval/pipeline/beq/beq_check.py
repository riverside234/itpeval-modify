from __future__ import annotations

import argparse
import json
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

from eval.pipeline.beq.beq import beq_check
from eval.pipeline.config import STMTS_JSON, RESULTS_DIR
from eval.pipeline.jsonl import load_checkpoint, load_jsonl, write_jsonl_atomic
from eval.pipeline.records import translation_record_key, translation_record_label


BEQ_DIR = RESULTS_DIR / "beq"


def _load_stmts_lookup(stmts_path: Path) -> dict[tuple[int, str, str], str]:
    """Load stmts.json into (theorem_id, title, prover) -> content."""
    data = json.loads(stmts_path.read_text())
    return {
        (e["theorem_id"], e["title"], e["prover"]): e["content"]
        for e in data
    }


def _make_beq_fields(
    *, beq=False, fwd=False, bwd=False,
    fwd_tactic="", bwd_tactic="",
    fwd_ms=0, bwd_ms=0,
    fwd_error="", bwd_error="",
    extraction_error="",
) -> dict:
    return {
        "beq": beq,
        "beq_forward": fwd,
        "beq_backward": bwd,
        "beq_forward_tactic": fwd_tactic,
        "beq_backward_tactic": bwd_tactic,
        "beq_forward_ms": fwd_ms,
        "beq_backward_ms": bwd_ms,
        "beq_forward_error": fwd_error,
        "beq_backward_error": bwd_error,
        "beq_extraction_error": extraction_error,
    }


def _run_beq(record: dict, stmts_lookup: dict) -> dict:
    """Run BEq for one record."""
    if not record.get("verified"):
        # BEq is only meaningful after native target verification succeeds
        return {**record, **_make_beq_fields(fwd_error="skipped: not verified",
                                              bwd_error="skipped: not verified")}

    if record.get("tgt_prover") != "lean4":
        msg = f"skipped: BEq is reported for lean4 targets, got {record.get('tgt_prover')}"
        return {**record, **_make_beq_fields(fwd_error=msg, bwd_error=msg)}

    generated = record.get("generated", "") or ""
    if not generated:
        return {**record, **_make_beq_fields(fwd_error="skipped: no generated content",
                                              bwd_error="skipped: no generated content")}

    ref_key = (record["theorem_id"], record["title"], record["tgt_prover"])
    reference = stmts_lookup.get(ref_key)
    if reference is None:
        # The reference statement comes from eval/data/stmts.json
        return {**record, **_make_beq_fields(
            fwd_error=f"reference not found: {ref_key}",
            bwd_error=f"reference not found: {ref_key}",
        )}

    try:
        r = beq_check(record["tgt_prover"], generated, reference)
    except Exception as e:
        return {**record, **_make_beq_fields(extraction_error=f"beq_check error: {e}")}
    return {**record, **_make_beq_fields(
        beq=r.equivalent,
        fwd=r.forward_ok, bwd=r.backward_ok,
        fwd_tactic=r.forward_tactic, bwd_tactic=r.backward_tactic,
        fwd_ms=r.forward_ms, bwd_ms=r.backward_ms,
        fwd_error=r.forward_error, bwd_error=r.backward_error,
        extraction_error=r.extraction_error,
    )}


def _result_tag(result: dict) -> str:
    if result.get("beq_extraction_error"):
        return "EXTRACT_FAIL"
    if result["beq"]:
        return "BEQ"
    if result["beq_forward"] or result["beq_backward"]:
        return "PARTIAL"
    return "FAIL"


def _write_checkpoint_result(result: dict, done_map: dict, ckpt_file) -> None:
    done_map[translation_record_key(result)] = result
    ckpt_file.write(json.dumps(result, ensure_ascii=False) + "\n")
    ckpt_file.flush()


def _run_lean4_parallel(
    records: list[dict],
    stmts_lookup: dict,
    done_map: dict,
    ckpt_file,
    workers: int,
) -> None:
    lean4_beq: list[dict] = []
    for r in records:
        if not r.get("verified"):
            result = _run_beq(r, stmts_lookup)
            _write_checkpoint_result(result, done_map, ckpt_file)
            continue
        gen = r.get("generated", "") or ""
        if not gen:
            result = _run_beq(r, stmts_lookup)
            _write_checkpoint_result(result, done_map, ckpt_file)
            continue
        ref_key = (r["theorem_id"], r["title"], r["tgt_prover"])
        if stmts_lookup.get(ref_key) is None:
            result = _run_beq(r, stmts_lookup)
            _write_checkpoint_result(result, done_map, ckpt_file)
            continue
        lean4_beq.append(r)

    if not lean4_beq:
        return

    print(f"  Running {len(lean4_beq)} lean4 BEq candidates "
          f"(workers={workers})...", flush=True)
    done_count = 0
    with ThreadPoolExecutor(max_workers=workers) as pool:
        futures = {pool.submit(_run_beq, r, stmts_lookup): r for r in lean4_beq}
        for fut in as_completed(futures):
            source_record = futures[fut]
            try:
                result = fut.result()
            except Exception as e:
                result = {**source_record, **_make_beq_fields(
                    extraction_error=f"beq_check error: {e}",
                )}
            _write_checkpoint_result(result, done_map, ckpt_file)
            done_count += 1
            print(f"    [{done_count}/{len(lean4_beq)}] {_result_tag(result)}  "
                  f"{translation_record_label(result)}", flush=True)


def beq_verify_file(
    input_path: Path,
    stmts_lookup: dict,
    workers: int,
    *,
    source_filter: str | None = None,
    target_filter: str | None = None,
) -> Path:
    records = load_jsonl(input_path)

    if source_filter:
        records = [r for r in records if r.get("source") == source_filter]
    if target_filter:
        records = [r for r in records if r.get("tgt_prover") == target_filter]

    total = len(records)
    lean4_verified = [
        r for r in records
        if r.get("verified") and r.get("tgt_prover") == "lean4"
    ]
    print(f"{input_path.name}: {total} entries, {len(lean4_verified)} verified lean4 BEq candidates")

    out_path = BEQ_DIR / input_path.name
    BEQ_DIR.mkdir(parents=True, exist_ok=True)
    ckpt_path = out_path.with_suffix(out_path.suffix + ".ckpt.jsonl")

    done_map = load_checkpoint(ckpt_path, translation_record_key)
    remaining = [r for r in records if translation_record_key(r) not in done_map]

    if done_map:
        print(f"  Checkpoint: {len(done_map)} done, {len(remaining)} remaining", flush=True)
    if not remaining:
        print("  All done (from checkpoint).", flush=True)
    else:
        remaining_lean4_verified = [
            r for r in remaining
            if r.get("verified") and r.get("tgt_prover") == "lean4"
        ]
        remaining_unverified = [r for r in remaining if not r.get("verified")]
        remaining_non_lean_verified = [
            r for r in remaining
            if r.get("verified") and r.get("tgt_prover") != "lean4"
        ]
        print(
            f"  To process: {len(remaining_lean4_verified)} lean4 BEq checks, "
            f"{len(remaining_unverified)} unverified skips, "
            f"{len(remaining_non_lean_verified)} non-lean skips",
            flush=True,
        )

    lean4_remaining = [r for r in remaining if r.get("tgt_prover") == "lean4"]
    other_remaining = [r for r in remaining if r.get("tgt_prover") != "lean4"]

    # Store skip records too so reruns do not repeatedly revisit them
    ckpt_path.parent.mkdir(parents=True, exist_ok=True)
    with ckpt_path.open("a", encoding="utf-8") as ckpt:
        if lean4_remaining:
            print(f"  Running {len(lean4_remaining)} lean4 entries...",
                  flush=True)
            _run_lean4_parallel(lean4_remaining, stmts_lookup, done_map, ckpt, workers)

        if other_remaining:
            print(f"  Skipping {len(other_remaining)} non-lean4 entries.",
                  flush=True)
            for r in other_remaining:
                result = _run_beq(r, stmts_lookup)
                done_map[translation_record_key(result)] = result
                ckpt.write(json.dumps(result, ensure_ascii=False) + "\n")
                ckpt.flush()

    write_jsonl_atomic(
        out_path,
        (
            done_map.get(
                translation_record_key(r),
                {**r, **_make_beq_fields(fwd_error="missing", bwd_error="missing")},
            )
            for r in records
        ),
    )

    out_records = load_jsonl(out_path)
    n_verified = sum(
        1 for r in out_records
        if r.get("verified") and r.get("tgt_prover") == "lean4"
    )
    n_beq = sum(1 for r in out_records if r.get("beq"))
    n_fwd = sum(1 for r in out_records if r.get("beq_forward"))
    n_bwd = sum(1 for r in out_records if r.get("beq_backward"))
    n_ext_fail = sum(
        1 for r in out_records
        if r.get("verified")
        and r.get("tgt_prover") == "lean4"
        and r.get("beq_extraction_error")
    )
    print(f"\n{input_path.name}: {n_beq}/{n_verified} verified entries BEq equivalent "
          f"(fwd={n_fwd}, bwd={n_bwd}, extract_fail={n_ext_fail})")
    print(f"Output: {out_path}")
    return out_path


def main() -> None:
    parser = argparse.ArgumentParser(description="Run BEq on verified statement translations.")
    parser.add_argument("files", nargs="+", help="Verified JSONL files to BEq-check")
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--source", type=str, default=None,
                        help="Filter to a specific source (e.g., minif2f)")
    parser.add_argument("--target", type=str, default=None,
                        help="Filter to a specific target prover (e.g., lean4)")
    args = parser.parse_args()

    stmts_lookup = _load_stmts_lookup(STMTS_JSON)
    print(f"Loaded {len(stmts_lookup)} reference entries from {STMTS_JSON}")

    for f in args.files:
        beq_verify_file(Path(f), stmts_lookup, args.workers,
                        source_filter=args.source, target_filter=args.target)


if __name__ == "__main__":
    main()
