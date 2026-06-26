"""Verify pre-generated proof translations from a generated JSONL file.

Usage:
    python -m eval.pipeline.translation.verify_generated eval/results/generated/proofs_claude-sonnet-4-6_20260426.jsonl
    python -m eval.pipeline.translation.verify_generated eval/results/generated/proofs_claude-sonnet-4-6_20260426.jsonl eval/results/generated/proofs_gpt-5.5_20260426.jsonl
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

from eval.pipeline.config import VERIFIED_DIR
from eval.pipeline.verify import verify


def _timeout_for(prover: str, *, hol_light_timeout_s: int | None = None) -> int:
    if prover == "hol-light" and hol_light_timeout_s is not None:
        return hol_light_timeout_s
    return {"lean4": 60, "rocq": 60, "isabelle": 120, "hol-light": 300}.get(prover, 120)


def _record_key(record: dict) -> str:
    """Stable key for generated records, including older files without custom_id."""
    custom_id = record.get("custom_id")
    if isinstance(custom_id, str) and custom_id:
        return custom_id
    return json.dumps(
        {
            "theorem_id": record.get("theorem_id"),
            "title": record.get("title"),
            "src_prover": record.get("src_prover"),
            "tgt_prover": record.get("tgt_prover"),
            "model": record.get("model"),
            "mode": record.get("mode"),
            "sample_idx": record.get("sample_idx"),
            "temperature": record.get("temperature"),
        },
        sort_keys=True,
        ensure_ascii=False,
    )


def _record_label(record: dict) -> str:
    custom_id = record.get("custom_id")
    if isinstance(custom_id, str) and custom_id:
        return custom_id
    return (
        f"{record.get('model', '?')} "
        f"{record.get('title', record.get('theorem_id', '?'))} "
        f"{record.get('src_prover', '?')}→{record.get('tgt_prover', '?')}"
    )


def _load_checkpoint(path: Path) -> dict[str, dict]:
    """Load partial results from a JSONL checkpoint file."""
    if not path.exists():
        return {}
    done: dict[str, dict] = {}
    with path.open("r", encoding="utf-8", errors="replace") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                r = json.loads(line)
            except json.JSONDecodeError:
                continue
            done[_record_key(r)] = r
    return done


def verify_file(input_path: Path, workers: int) -> Path:
    return _verify_file(
        input_path,
        workers,
        hol_light_timeout_s=None,
    )


def _verify_file(
    input_path: Path,
    workers: int,
    *,
    hol_light_timeout_s: int | None,
) -> Path:
    records = [json.loads(l) for l in input_path.read_text().splitlines() if l.strip()]
    total = len(records)
    print(f"{input_path.name}: {total} entries")

    out_path = VERIFIED_DIR / input_path.name.replace("generated/", "")
    VERIFIED_DIR.mkdir(parents=True, exist_ok=True)
    ckpt_path = out_path.with_suffix(out_path.suffix + ".ckpt.jsonl")

    done_map = _load_checkpoint(ckpt_path)
    if done_map:
        print(f"  Resuming from checkpoint: {ckpt_path} ({len(done_map)}/{total} done)", flush=True)

    done = 0

    def _run(r: dict) -> dict:
        generated = r.get("generated", "") or ""
        tgt_prover = r.get("tgt_prover", "")

        if generated and tgt_prover:
            vr = verify(
                tgt_prover,
                generated,
                timeout_s=_timeout_for(tgt_prover, hol_light_timeout_s=hol_light_timeout_s),
            )
            return {**r, "verified": vr.ok, "verify_error": vr.error, "verify_ms": vr.duration_ms}
        return {**r, "verified": False, "verify_error": "no output", "verify_ms": 0}

    remaining = [r for r in records if _record_key(r) not in done_map]
    if not remaining:
        print("  Nothing to do: all entries already in checkpoint.", flush=True)
    else:
        print(f"  Verifying: {len(remaining)} remaining (workers={workers})", flush=True)

    # Append-only checkpoint so we can resume after interruption.
    ckpt_path.parent.mkdir(parents=True, exist_ok=True)
    with ckpt_path.open("a", encoding="utf-8") as ckpt, ThreadPoolExecutor(max_workers=workers) as pool:
        futures = {pool.submit(_run, r): r for r in remaining}
        for fut in as_completed(futures):
            result = fut.result()
            done_map[_record_key(result)] = result
            ckpt.write(json.dumps(result, ensure_ascii=False) + "\n")
            ckpt.flush()
            done += 1
            status = "PASS" if result["verified"] else "FAIL"
            print(f"  [{done}/{total}] {status}  {_record_label(result)}", flush=True)

    tmp_path = out_path.with_suffix(out_path.suffix + ".tmp")
    with tmp_path.open("w", encoding="utf-8") as out:
        for r in records:
            key = _record_key(r)
            out.write(json.dumps(done_map.get(key, {**r, "verified": False, "verify_error": "missing", "verify_ms": 0}),
                                 ensure_ascii=False) + "\n")
    tmp_path.replace(out_path)

    passed = sum(
        1 for l in out_path.read_text().splitlines()
        if l.strip() and json.loads(l).get("verified")
    )
    print(f"\n{input_path.name}: {passed}/{total} passed")
    print(f"Output: {out_path}")
    return out_path


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("files", nargs="+", help="Generated JSONL files to verify")
    parser.add_argument("--workers", type=int, default=8,
                        help="Parallel verification workers (default: 8)")
    parser.add_argument(
        "--hol-light-timeout-s",
        type=int,
        default=None,
        help="Override per-entry HOL Light timeout in seconds (default: 300).",
    )
    args = parser.parse_args()

    for f in args.files:
        _verify_file(
            Path(f),
            args.workers,
            hol_light_timeout_s=args.hol_light_timeout_s,
        )


if __name__ == "__main__":
    main()
