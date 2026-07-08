from __future__ import annotations

import argparse
import json
import threading
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

from eval.pipeline.config import RESULTS_DIR
from eval.pipeline.jsonl import load_jsonl
from eval.pipeline.models import select_models
from eval.pipeline.verify import timeout_for, verify

CYCLE_DIR = RESULTS_DIR / "cycle"

_ITP_PROVER = {
    "lean4":     "lean4",
    "isabelle":  "isabelle",
    "rocq":      "rocq",
    "hol_light": "hol-light",
}
CYCLE1_FIELDS: list[tuple[str, str]] = [
    ("step1_lean4", "lean4"),
    ("step3_lean4", "lean4"),
]
CYCLE2_FIELDS: list[tuple[str, str]] = [
    (f"step{step}_{itp}", itp)
    for step in [1, 3]
    for itp in ["lean4", "isabelle", "rocq", "hol_light"]
]


def _verify_record(
    record: dict,
    fields: list[tuple[str, str]],
) -> dict:
    result = dict(record)
    for field, itp in fields:
        prover = _ITP_PROVER[itp]

        # Empty cycle sections are recorded without invoking the prover
        content = record.get(field, "")
        if not content:
            result[f"{field}_ok"]  = None
            result[f"{field}_err"] = "empty"
            result[f"{field}_ms"]  = 0
            continue

        vr = verify(prover, content, timeout_s=timeout_for(prover))
        result[f"{field}_ok"]  = vr.ok
        result[f"{field}_err"] = vr.error
        result[f"{field}_ms"]  = vr.duration_ms

    return result


def _load_done(out_path: Path) -> set[str]:
    done: set[str] = set()
    if not out_path.exists():
        return done
    for record in load_jsonl(out_path):
        done.add(record["name"])
    return done


def verify_cycle_file(
    input_path: Path,
    fields: list[tuple[str, str]],
    *,
    workers: int,
) -> Path:
    records = load_jsonl(input_path)
    out_path = input_path.with_name(input_path.stem + "_verified.jsonl")

    done = _load_done(out_path)
    # Cycle verification resumes by theorem name within each model output file
    remaining = [r for r in records if r["name"] not in done]
    total = len(records)

    print(f"\n{input_path.name}: {total} records, {len(done)} done, {len(remaining)} remaining")
    if not remaining:
        print("  Nothing to do.")
        _print_summary(out_path, fields)
        return out_path

    done_count = len(done)
    write_lock = threading.Lock()

    with out_path.open("a", encoding="utf-8") as out_f:
        with ThreadPoolExecutor(max_workers=workers) as pool:
            futures = {
                pool.submit(_verify_record, r, fields): r
                for r in remaining
            }
            for fut in as_completed(futures):
                try:
                    result = fut.result()
                except Exception as e:
                    print(f"  [error] {e}", flush=True)
                    continue
                with write_lock:
                    out_f.write(json.dumps(result, ensure_ascii=False) + "\n")
                    out_f.flush()
                    done_count += 1
                passes = [f for f, _ in fields if result.get(f"{f}_ok") is True]
                fails  = [f for f, _ in fields if result.get(f"{f}_ok") is False]
                print(
                    f"  [{done_count}/{total}] {result['name']}: "
                    f"{len(passes)} pass  {len(fails)} fail",
                    flush=True,
                )

    _print_summary(out_path, fields)
    return out_path


def _print_summary(out_path: Path, fields: list[tuple[str, str]]) -> None:
    if not out_path.exists():
        return
    recs = load_jsonl(out_path)
    print(f"\n  Summary ({out_path.name}):")
    for field, _ in fields:
        ok_key  = f"{field}_ok"
        err_key = f"{field}_err"
        verified = [r for r in recs if r.get(ok_key) is not None
                    and r.get(err_key) != "empty"]
        n_pass = sum(1 for r in verified if r.get(ok_key) is True)
        n_tot  = len(verified)
        empty  = sum(1 for r in recs if r.get(err_key) == "empty")
        note = ""
        if empty:
            note += f"  ({empty} empty)"
        bar = f"{n_pass}/{n_tot}" if n_tot else "—"
        print(f"    {field:30s}  {bar}{note}")


def main() -> None:
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("--cycle",   choices=["1", "2", "both"], default="both",
                        help="Which cycle(s) to verify (default: both)")
    parser.add_argument("--model",   default=None,
                        help="Model label(s), comma-separated (default: all)")
    parser.add_argument("--workers", type=int, default=4,
                        help="Parallel workers (records verified simultaneously, default: 4)")
    args = parser.parse_args()

    model_labels = [m["label"] for m in select_models(args.model)]

    cycles = [1, 2] if args.cycle == "both" else [int(args.cycle)]

    for cycle in cycles:
        fields = CYCLE1_FIELDS if cycle == 1 else CYCLE2_FIELDS
        print(f"\n=== Cycle {cycle} — verifying {len(fields)} field(s) per record ===")
        for label in model_labels:
            path = CYCLE_DIR / f"cycle{cycle}" / f"{label}.jsonl"
            if not path.exists():
                print(f"  {path.name}: not found, skipping")
                continue
            verify_cycle_file(path, fields, workers=args.workers)


if __name__ == "__main__":
    main()
