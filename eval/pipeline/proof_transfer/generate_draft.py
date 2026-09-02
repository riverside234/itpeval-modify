from __future__ import annotations

import argparse
import hashlib
import json
import sys
import time
from collections.abc import Iterable
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from eval.pipeline.proof_transfer.aligned_data import (
    LAB_REPO_ROOT,
    resolved_repo_root,
    validate_repo_layout,
)
from eval.pipeline.proof_transfer.llm import (
    DEFAULT_DRAFT_MODEL,
    DEFAULT_REASONING_EFFORT,
    DraftModelConfig,
    ReasoningEffort,
    call_draft_model,
)
from eval.pipeline.proof_transfer.prompt import (
    DraftPrompt,
    build_draft_prompt,
    normalize_draft_content,
)


DEFAULT_RECORDS_INPUT = (
    "eval/results/proof_transfer/babel_formal_v1_exact_name_records.jsonl"
)
DEFAULT_DRAFTS_OUTPUT = "eval/results/proof_transfer/babel_formal_v1_drafts.jsonl"


def _print_json(data: Any) -> None:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    print(json.dumps(data, indent=2, ensure_ascii=False))


def resolve_repo_path(path: str | Path) -> Path:
    root = resolved_repo_root()
    resolved = Path(path).expanduser()
    if not resolved.is_absolute():
        resolved = root / resolved
    resolved = resolved.resolve(strict=False)
    try:
        resolved.relative_to(root)
    except ValueError as exc:
        raise SystemExit(f"path must be inside repo root {root}: {resolved}") from exc
    return resolved


def read_jsonl(path: str | Path) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    input_path = resolve_repo_path(path)
    with input_path.open("r", encoding="utf-8") as handle:
        for line_number, line in enumerate(handle, start=1):
            line = line.strip()
            if not line:
                continue
            try:
                record = json.loads(line)
            except json.JSONDecodeError as exc:
                raise ValueError(f"invalid JSONL at {input_path}:{line_number}") from exc
            if not isinstance(record, dict):
                raise ValueError(f"expected object at {input_path}:{line_number}")
            records.append(record)
    return records


def append_jsonl(path: str | Path, record: dict[str, Any]) -> None:
    output_path = resolve_repo_path(path)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with output_path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(record, ensure_ascii=False) + "\n")


def write_jsonl(path: str | Path, records: Iterable[dict[str, Any]]) -> None:
    output_path = resolve_repo_path(path)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    payload = "\n".join(json.dumps(record, ensure_ascii=False) for record in records)
    output_path.write_text(payload + ("\n" if payload else ""), encoding="utf-8")


def record_key(record: dict[str, Any]) -> tuple[str, int, str, str]:
    try:
        return (
            str(record["source"]),
            int(record["theorem_id"]),
            str(record["topic"]),
            str(record["target_key"]),
        )
    except KeyError as exc:
        raise ValueError(f"record is missing key field {exc.args[0]!r}") from exc


def _record_matches(
    record: dict[str, Any],
    *,
    topic: str | None,
    target_key: str | None,
) -> bool:
    if topic is not None and record.get("topic") != topic:
        return False
    if target_key is not None and record.get("target_key") != target_key:
        return False
    return True


def select_records(
    records: Iterable[dict[str, Any]],
    *,
    topic: str | None = None,
    target_key: str | None = None,
    limit: int | None = None,
) -> list[dict[str, Any]]:
    selected = [
        record
        for record in records
        if _record_matches(record, topic=topic, target_key=target_key)
    ]
    if limit is not None:
        selected = selected[:limit]
    return selected


def completed_draft_keys(path: str | Path) -> set[tuple[str, int, str, str]]:
    output_path = resolve_repo_path(path)
    if not output_path.exists():
        return set()

    completed: set[tuple[str, int, str, str]] = set()
    for record in read_jsonl(output_path):
        if record.get("draft") and not record.get("draft_error"):
            completed.add(record_key(record))
    return completed


def _prompt_sha256(prompt: DraftPrompt) -> str:
    content = "\n\n".join([prompt.system_prompt, prompt.user_prompt])
    return hashlib.sha256(content.encode("utf-8")).hexdigest()


def generate_draft_record(
    record: dict[str, Any],
    *,
    config: DraftModelConfig,
    continue_on_error: bool = True,
) -> dict[str, Any]:
    """Generate and attach the content-only Draft for one parsed V1 record."""
    prompt = build_draft_prompt(record)
    result = dict(record)
    result["draft_prompt_version"] = prompt.prompt_version
    result["draft_prompt_sha256"] = _prompt_sha256(prompt)
    result["draft_model"] = config.to_metadata()
    result["draft_generated_at"] = datetime.now(timezone.utc).isoformat()

    start = time.monotonic()
    try:
        draft = call_draft_model(
            system_prompt=prompt.system_prompt,
            user_prompt=prompt.user_prompt,
            config=config,
        )
        result["draft"] = normalize_draft_content(draft)
        result["draft_error"] = None
    except Exception as exc:
        if not continue_on_error:
            raise
        result["draft"] = ""
        result["draft_error"] = f"{type(exc).__name__}: {exc}"
    finally:
        result["draft_duration_seconds"] = round(time.monotonic() - start, 3)

    return result


def generate_drafts(
    *,
    input_path: str | Path = DEFAULT_RECORDS_INPUT,
    output_path: str | Path = DEFAULT_DRAFTS_OUTPUT,
    topic: str | None = None,
    target_key: str | None = None,
    limit: int | None = None,
    model: str = DEFAULT_DRAFT_MODEL,
    reasoning_effort: ReasoningEffort = DEFAULT_REASONING_EFFORT,
    max_output_tokens: int = 16000,
    resume: bool = True,
    continue_on_error: bool = True,
    dry_run: bool = False,
) -> int:
    records = select_records(
        read_jsonl(input_path),
        topic=topic,
        target_key=target_key,
        limit=limit,
    )
    if not records:
        raise SystemExit("No input records matched the requested filters.")

    if dry_run:
        prompt = build_draft_prompt(records[0])
        _print_json(
            {
                "dry_run": True,
                "selected_records": len(records),
                "first_record_key": record_key(records[0]),
                "prompt_version": prompt.prompt_version,
                "system_prompt": prompt.system_prompt,
                "user_prompt": prompt.user_prompt,
            }
        )
        return 0

    skipped_keys = completed_draft_keys(output_path) if resume else set()
    output = resolve_repo_path(output_path)
    if not resume:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text("", encoding="utf-8")

    config = DraftModelConfig(
        model=model,
        reasoning_effort=reasoning_effort,
        max_output_tokens=max_output_tokens,
    )

    written = 0
    total = len(records)
    for index, record in enumerate(records, start=1):
        key = record_key(record)
        if key in skipped_keys:
            print(f"[{index}/{total}] skip existing draft {key[2]}/{key[3]}", file=sys.stderr)
            continue

        print(f"[{index}/{total}] draft {key[2]}/{key[3]}", file=sys.stderr)
        drafted = generate_draft_record(
            record,
            config=config,
            continue_on_error=continue_on_error,
        )
        append_jsonl(output, drafted)
        written += 1

    print(f"Wrote {written} new draft record(s) to {output}")
    return written


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Generate Isabelle-proof-derived Drafts for parsed Babel Formal records."
    )
    parser.add_argument("--expected-root", help=f"Expected repo root, e.g. {LAB_REPO_ROOT}.")
    parser.add_argument("--check-layout", action="store_true", help="Validate repo/input paths and exit.")
    parser.add_argument("--input", default=DEFAULT_RECORDS_INPUT, help="Parsed V1 records JSONL.")
    parser.add_argument("--output", default=DEFAULT_DRAFTS_OUTPUT, help="Draft records JSONL.")
    parser.add_argument("--topic", help="Optional Babel Formal topic filter.")
    parser.add_argument("--target-key", help="Optional local target theorem filter.")
    parser.add_argument("--limit", type=int, help="Optional maximum number of selected records.")
    parser.add_argument("--model", default=DEFAULT_DRAFT_MODEL)
    parser.add_argument("--reasoning-effort", default=DEFAULT_REASONING_EFFORT)
    parser.add_argument("--max-output-tokens", type=int, default=16000)
    parser.add_argument("--resume", dest="resume", action="store_true", default=True)
    parser.add_argument("--no-resume", dest="resume", action="store_false")
    parser.add_argument("--continue-on-error", dest="continue_on_error", action="store_true", default=True)
    parser.add_argument("--fail-fast", dest="continue_on_error", action="store_false")
    parser.add_argument("--dry-run", action="store_true", help="Print the first prompt and do not call the API.")
    args = parser.parse_args()

    if args.expected_root or args.check_layout:
        layout = validate_repo_layout(args.expected_root)
        if args.check_layout:
            _print_json(layout)
            return

    generate_drafts(
        input_path=args.input,
        output_path=args.output,
        topic=args.topic,
        target_key=args.target_key,
        limit=args.limit,
        model=args.model,
        reasoning_effort=args.reasoning_effort,
        max_output_tokens=args.max_output_tokens,
        resume=args.resume,
        continue_on_error=args.continue_on_error,
        dry_run=args.dry_run,
    )


if __name__ == "__main__":
    main()
