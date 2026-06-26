from __future__ import annotations

import argparse
import json
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

import openai

from eval.pipeline.batch import poll, submit
from eval.pipeline.config import BATCH_JOBS_DIR, MODELS, VERIFIED_DIR
from eval.pipeline.translation.data import load_pairs
from eval.pipeline.translation.prompt import build_prompt
from eval.pipeline.verify import verify

POLL_INTERVAL_S = 60  # seconds between status checks
GEMINI_CHUNK_SIZE = 200  # requests per chunk (~4M tokens at 16k output each, safe for proofs)


def _make_request(pair: dict, mode: str) -> dict:
    system_prompt, user_prompt = build_prompt(
        title=pair["title"],
        src_prover=pair["src_prover"],
        tgt_prover=pair["tgt_prover"],
        source_content=pair["src_content"],
        mode=mode,
    )
    custom_id = f"{pair['source']}__{pair['theorem_id']}__{pair['src_prover']}__{pair['tgt_prover']}"
    return {
        "custom_id":     custom_id,
        "system_prompt": system_prompt,
        "user_prompt":   user_prompt,
        "_theorem_id":   pair["theorem_id"],
        "_title":        pair["title"],
        "_source":       pair["source"],
        "_tier":         pair["tier"],
        "_src_prover":   pair["src_prover"],
        "_tgt_prover":   pair["tgt_prover"],
    }


def _chunk(lst: list, size: int) -> list[list]:
    return [lst[i:i + size] for i in range(0, len(lst), size)]


def _submit_with_retry(model_cfg: dict, requests: list[dict], max_retries: int = 5) -> str:
    """Submit with exponential backoff on 429 rate-limit errors and transient timeouts."""
    import requests as http_mod
    import httpx
    delay = 60
    for attempt in range(max_retries):
        try:
            return submit(model_cfg, requests)
        except http_mod.exceptions.HTTPError as e:
            if e.response is not None and e.response.status_code == 429 and attempt < max_retries - 1:
                print(f"  429 rate limit — retrying in {delay}s ...", flush=True)
                time.sleep(delay)
                delay *= 2
            else:
                raise
        except (httpx.WriteTimeout, httpx.ReadTimeout, httpx.ConnectTimeout) as e:
            if attempt < max_retries - 1:
                print(f"  network timeout ({e.__class__.__name__}) — retrying in {delay}s ...", flush=True)
                time.sleep(delay)
                delay *= 2
            else:
                raise


PROOFS_SOURCES = ["babel-formal", "hundred-theorems"]


def cmd_submit(args: argparse.Namespace) -> None:
    if args.sources:
        sources = args.sources.split(",")
    elif args.mode == "proofs":
        sources = PROOFS_SOURCES
    else:
        sources = None
    ids = [int(x) for x in args.ids.split(",")] if getattr(args, "ids", None) else None
    subset = None
    if getattr(args, "subset", None):
        subset_items = json.loads(Path(args.subset).read_text(encoding="utf-8"))
        subset = {(it["source"], int(it["theorem_id"])) for it in subset_items}
    pairs = load_pairs(args.mode, sources=sources, theorem_ids=ids, subset=subset)
    print(f"Loaded {len(pairs)} pairs (mode={args.mode})")

    wanted_labels = set(args.models.split(",")) if args.models else None
    models = [m for m in MODELS if not wanted_labels or m["label"] in wanted_labels]
    if not models:
        sys.exit(f"No models matched: {wanted_labels}")

    BATCH_JOBS_DIR.mkdir(exist_ok=True)
    timestamp = datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%S")
    job_file = BATCH_JOBS_DIR / f"{timestamp}.json"

    job_data: dict = {
        "submitted_at": datetime.now(timezone.utc).isoformat(),
        "mode":         args.mode,
        "sources":      sources,
        "models":       {},
        "requests":     [],
    }

    for model_cfg in models:
        label = model_cfg["label"]
        requests = [_make_request(p, args.mode) for p in pairs]

        api_requests = [
            {k: v for k, v in r.items() if not k.startswith("_")}
            for r in requests
        ]

        if not job_data["requests"]:
            job_data["requests"] = [
                {k: v for k, v in r.items() if k.startswith("_")}
                | {"custom_id": r["custom_id"]}
                for r in requests
            ]

        job_data["models"][label] = {
            "provider":  model_cfg["provider"],
            "model_id":  model_cfg["id"],
            "batch_ids": [],
            "status":    "submitted",
        }

        if model_cfg["provider"] == "gemini":
            chunks = _chunk(api_requests, GEMINI_CHUNK_SIZE)
            print(f"Submitting {len(api_requests)} requests for {label} "
                  f"in {len(chunks)} chunk(s) ...", flush=True)
            for i, chunk in enumerate(chunks):
                print(f"  chunk {i+1}/{len(chunks)} ({len(chunk)} requests) ...", flush=True)
                bid = _submit_with_retry(model_cfg, chunk)
                job_data["models"][label]["batch_ids"].append(bid)
                job_file.write_text(json.dumps(job_data, indent=2, ensure_ascii=False))
                print(f"    {bid}")
        else:
            print(f"Submitting {len(api_requests)} requests for {label} ...", flush=True)
            bid = submit(model_cfg, api_requests)
            job_data["models"][label]["batch_ids"] = [bid]
            job_file.write_text(json.dumps(job_data, indent=2, ensure_ascii=False))
            print(f"  {label}: {bid}")

    print(f"\nJob file: {job_file}")
    print(f"Run: python -m eval.pipeline.translation.batch_run collect {job_file}")


def cmd_collect(args: argparse.Namespace) -> None:
    job_file = Path(args.job_file)
    job_data = json.loads(job_file.read_text())

    meta = {r["custom_id"]: r for r in job_data["requests"]}
    model_by_label = {m["label"]: m for m in MODELS}

    for info in job_data["models"].values():
        if "batch_id" in info and "batch_ids" not in info:
            info["batch_ids"] = [info["batch_id"]] if info["batch_id"] else []

    pending: dict[str, list[str]] = {}
    collected: dict[str, dict[str, str]] = {}  # label → {custom_id: text}

    for label, info in job_data["models"].items():
        if info["status"] in ("completed", "failed", "expired", "cancelled"):
            collected[label] = info.get("results", {})
            continue
        pending[label] = list(info["batch_ids"])
        collected[label] = {}

    if pending:
        print(f"Polling {list(pending)} ...")

    while pending:
        time.sleep(POLL_INTERVAL_S)
        still_pending: dict[str, list[str]] = {}

        for label, batch_ids in pending.items():
            info = job_data["models"][label]
            model_cfg = model_by_label[label]
            remaining_ids = []

            for bid in batch_ids:
                try:
                    status, results = poll(model_cfg, bid)
                except (openai.APIConnectionError, Exception) as e:
                    print(f"  {label} [{bid[:20]}]: transient error ({e}), will retry")
                    remaining_ids.append(bid)
                    continue

                print(f"  {label} [{bid[:20]}...]: {status}")

                if status == "completed" and results is not None:
                    collected[label].update(results)
                elif status in ("failed", "expired", "cancelled"):
                    print(f"  {label} [{bid[:20]}]: chunk {status}, skipping")
                else:
                    remaining_ids.append(bid)

            if remaining_ids:
                still_pending[label] = remaining_ids
            else:
                info["status"] = "completed"
                info["results"] = collected[label]
                job_file.write_text(json.dumps(job_data, indent=2, ensure_ascii=False))

        pending = still_pending

    VERIFIED_DIR.mkdir(parents=True, exist_ok=True)
    mode = job_data["mode"]
    timestamp = datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%S")
    results_path = VERIFIED_DIR / f"batch_{mode}_{timestamp}.jsonl"
    print(f"\nVerifying and writing results to {results_path} ...")

    total = sum(len(v) for v in collected.values())
    done = 0

    with results_path.open("w", encoding="utf-8") as out:
        for label, results in collected.items():
            info = job_data["models"][label]
            model_id = info["model_id"]
            for custom_id, generated in results.items():
                done += 1
                m = meta.get(custom_id, {})
                tgt_prover = m.get("_tgt_prover", "")

                print(f"[{done}/{total}] {label}  {custom_id}", end=" ", flush=True)

                if generated and tgt_prover:
                    vr = verify(tgt_prover, generated)
                    verified, verify_error, verify_ms = vr.ok, vr.error, vr.duration_ms
                else:
                    verified, verify_error, verify_ms = False, "no output", 0

                status = "PASS" if verified else "FAIL"
                print(status)

                record = {
                    "theorem_id":   m.get("_theorem_id"),
                    "title":        m.get("_title"),
                    "source":       m.get("_source"),
                    "tier":         m.get("_tier"),
                    "src_prover":   m.get("_src_prover"),
                    "tgt_prover":   tgt_prover,
                    "model":        label,
                    "model_id":     model_id,
                    "mode":         mode,
                    "generated":    generated,
                    "verified":     verified,
                    "verify_error": verify_error,
                    "verify_ms":    verify_ms,
                }
                out.write(json.dumps(record, ensure_ascii=False) + "\n")
                out.flush()

    print(f"\nDone. Results: {results_path}")


def main() -> None:
    parser = argparse.ArgumentParser(prog="batch_run")
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_submit = sub.add_parser("submit", help="Submit batch jobs")
    p_submit.add_argument("--mode",    choices=["stmts", "proofs"], default="proofs",
                          help="stmts: translate sorry-filled statements; proofs: translate full proofs (default: proofs)")
    p_submit.add_argument("--sources", help="Comma-separated benchmark names (default: all)")
    p_submit.add_argument("--ids",     help="Comma-separated theorem IDs to include (default: all)")
    p_submit.add_argument(
        "--subset",
        help="Path to a subset JSON file (list of {source,theorem_id}) to restrict evaluation",
    )
    p_submit.add_argument("--models",  help="Comma-separated model labels (default: all in config)")

    p_collect = sub.add_parser("collect", help="Poll, verify, and write results")
    p_collect.add_argument("job_file", help="Path to the .json job file from submit")

    args = parser.parse_args()
    if args.cmd == "submit":
        cmd_submit(args)
    else:
        cmd_collect(args)


if __name__ == "__main__":
    main()
