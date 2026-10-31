"""DSP-specific input, cohort and artifact identities (independent of v2_itpeval)."""
from __future__ import annotations

import json
from pathlib import Path

from ..common import (fingerprint, key, public_record, read_jsonl, repo_path,
                      require_source, select, sha256, summarize, write_jsonl)
from ..inventory import inventory_hol_declarations
from ..theory_context import validate_context, normalize_body
from ..isabelle_syntax import tokens

SCHEMA_VERSION = "hol_light_to_isabelle_dsp_v2"
ISABELLE_VERSION = "Isabelle2026"
MODES = ("draft", "hol-light-proof")
CONTEXT_FIELDS = ("isabelle_statement", "isabelle_theory_template",
                  "isabelle_context_before_target", "isabelle_proof_prefix",
                  "isabelle_target_proof_span", "isabelle_target_name")
SOURCE_FIELDS = ("hol_light_statement", "hol_light_proof", "hol_light_reference_context")


def validate_mode(mode: str) -> str:
    if mode not in MODES:
        raise ValueError("sketch_source must be draft or hol-light-proof")
    return mode


def clean_record(record: dict, mode: str) -> dict:
    result = public_record(record)
    if validate_mode(mode) == "hol-light-proof":
        result = {k: v for k, v in result.items()
                  if (k == "draft_used" or not k.startswith("draft")) and k != "informal_proof"}
    return result


def mode_of(record: dict, default: str = "draft") -> str:
    return validate_mode(record.get("sketch_source", default))


def envelope(mode: str) -> dict:
    return {"schema_version": SCHEMA_VERSION, "pipeline": "v2-dsp",
            "sketch_source": validate_mode(mode), "draft_used": mode == "draft",
            "expected_isabelle_version": ISABELLE_VERSION}


def require_text(record: dict, name: str) -> str:
    value = record.get(name)
    if not isinstance(value, str) or not value.strip():
        raise ValueError("missing nonempty " + name)
    return value


def input_metadata(record: dict, sketch_source: str = "draft") -> dict:
    mode = validate_mode(sketch_source)
    if record.get("sketch_source", mode) != mode:
        raise ValueError("input Sketch mode differs from requested mode")
    if record.get("input_error"):
        raise ValueError(record["input_error"])
    context = validate_context(record)
    metadata = {**context.metadata, **envelope(mode)}
    if mode == "draft":
        draft = require_text(record, "draft")
        if record.get("draft_error"):
            raise ValueError("a successful saved mathematical Draft is required")
        metadata["draft_sha256"] = sha256(draft)
        consumed = {"draft": draft}
    else:
        consumed = {name: require_text(record, name) for name in SOURCE_FIELDS}
        reference = consumed["hol_light_reference_context"]
        masked = inventory_hol_declarations(reference, masked=True)
        name = require_text(record, "hol_light_target_name")
        matches = [item for item in masked if item.name == name]
        if len(matches) != 1 or " ".join(matches[0].statement.split()) != " ".join(
                consumed["hol_light_statement"].split()):
            raise ValueError("selected HOL Light statement does not match masked reference")
        if consumed["hol_light_proof"].strip().upper() in {"SORRY", "ADMIT", ""}:
            raise ValueError("direct mode requires the completed selected HOL Light proof")
        expected = record.get("metadata", {}).get("hol_light_stmt_sha256")
        if expected and sha256(reference) != expected:
            raise ValueError("proof-masked HOL Light reference hash mismatch")
        metadata.update({name + "_sha256": sha256(value) for name, value in consumed.items()})
        metadata.pop("draft_context_policy", None)
    metadata["input_fingerprint"] = fingerprint({
        **envelope(mode), "consumed": consumed,
        "target_context": {name: record.get(name, "") for name in CONTEXT_FIELDS},
        "metadata": record.get("metadata"),
    })
    if record.get("sketch_fingerprint") and record.get("input_fingerprint") != metadata["input_fingerprint"]:
        raise ValueError("stale saved Sketch input fingerprint")
    return metadata


def validate_artifacts(records: list[dict], mode: str) -> None:
    """Reject mixed/legacy outputs even when only an unrelated target was selected."""
    for row in records:
        if (row.get("schema_version") != SCHEMA_VERSION or row.get("pipeline") != "v2-dsp"
                or row.get("sketch_source") != mode
                or row.get("expected_isabelle_version") != ISABELLE_VERSION
                or row.get("draft_used") is not (mode == "draft")):
            raise ValueError("incompatible DSP artifact: use a separate Isabelle2026/mode output file; "
                             "old PISA results cannot be resumed")
        backend = row.get("backend_metadata") or {}
        if backend and (backend.get("backend") != "isabelle-native"
                        or backend.get("isabelle_version") != ISABELLE_VERSION):
            raise ValueError("incompatible native backend in reused DSP artifact")


def load_inputs(path, *, mode: str, samples: bool = False, artifacts: bool = False,
                topic=None, target_key=None, limit=None) -> list[dict]:
    rows = read_jsonl(path)
    if artifacts:
        validate_artifacts(rows, mode)
    else:
        for row in rows:
            if row.get("pipeline") == "v2-dsp":
                validate_artifacts([row], mode)
            elif row.get("sketch_source", mode) != mode:
                raise ValueError("mixed Sketch input modes")
    latest = {}
    for row in rows:
        identity = (key(row), int(row["sample_idx"])) if samples else key(row)
        latest[identity] = clean_record(row, mode)
    selected = select(latest.values(), topic=topic, target_key=target_key)
    if limit is not None:
        if limit < 1:
            raise ValueError("limit must be positive")
        wanted = list(dict.fromkeys(key(row) for row in selected))[:limit]
        selected = [row for row in selected if key(row) in wanted]
    return selected


def align_samples(records: list[dict], expected: list[dict] | None, samples: int | None,
                  *, mode: str) -> list[dict]:
    if expected is None:
        return records
    if samples is None or samples < 1:
        raise ValueError("expected_samples must be positive with a target cohort")
    latest = {(key(row), int(row["sample_idx"])): row for row in records}
    result = []
    fields = CONTEXT_FIELDS + (("draft", "draft_error") if mode == "draft" else SOURCE_FIELDS)
    for target in expected:
        for index in range(samples):
            row = latest.get((key(target), index))
            if row is not None and mode_of(row) == mode and all(
                    row.get(name, "") == target.get(name, "") for name in fields):
                result.append(row)
            else:
                result.append({**clean_record(target, mode), **envelope(mode), "sample_idx": index,
                               "sketch_error": "missing or stale Sketch for selected input/context",
                               "failure_category": "missing_sketch"})
    return result


def save_results(path, records: list[dict], *, mode: str, preserve_unselected=False,
                 expected=None, expected_samples=None) -> dict:
    validate_artifacts(records, mode)
    previous = read_jsonl(path) if repo_path(path).is_file() else []
    validate_artifacts(previous, mode)
    active = {(key(row), int(row["sample_idx"])) for row in records}
    retained = [row for row in previous if (key(row), int(row["sample_idx"])) not in active]
    write_jsonl(path, (retained if preserve_unselected else []) + records)
    summary = summarize(records, expected=expected, expected_samples=expected_samples)
    summary.update(envelope(mode))
    summary["missing_samples"] = summary.get("missing_samples", 0) + sum(
        row.get("failure_category") == "missing_sketch" for row in records)
    # Count the shared Draft once per target, and Sketch usage once per sample.
    def usage(rows, field):
        totals = {}
        for row in rows:
            for name, value in (row.get(field, {}).get("usage") or {}).items():
                if isinstance(value, (float, int)) and not isinstance(value, bool):
                    totals[name] = totals.get(name, 0) + value
        return totals
    unique = {key(row): row for row in expected or records}
    summary["llm_usage"] = {"draft": usage(unique.values(), "draft_response") if mode == "draft" else {},
                            "sketch": usage(records, "sketch_response")}
    repo_path(path).with_suffix(".summary.json").write_text(
        json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    return summary


def output_path(path, *, results_dir: str, filename: str, mode: str, config=None,
                records: list[dict] | None = None) -> str:
    if path is not None:
        return str(path)
    profile = "api"
    data = config.to_metadata() if config is not None else None
    if data is None and records:
        models = {fingerprint(r["sketch_model"]): r["sketch_model"] for r in records if r.get("sketch_model")}
        if len(models) == 1:
            data = next(iter(models.values()))
        elif models:
            profile = "mixed_sketch_models_" + fingerprint(sorted(models))[:10]
    if data is not None:
        profile = ("qwen_vllm" if data.get("provider") == "vllm" or data.get("backend") == "vllm" else "api") + "_" + fingerprint(data)[:10]
        if mode == "draft":
            providers = {(r.get("draft_model") or {}).get("provider", "openai") for r in records or []}
            if providers != {"openai"} and providers:
                profile = ("qwen_draft_" if providers == {"vllm"} else "mixed_drafts_") + profile
    return str(Path(results_dir) / "v2-dsp-isabelle2026" /
               ("direct" if mode == "hol-light-proof" else "draft") / profile / filename)


def normalize_sketch(proof: str) -> str:
    body = normalize_body(proof, allow_hammer=True)
    for token in tokens(body):
        if token.kind == "word" and token.text == "sledgehammer":
            start = body.rfind("\n", 0, token.start) + 1
            end = body.find("\n", token.end)
            if end < 0:
                end = len(body)
            if [t.text for t in tokens(body[start:end])] != ["sledgehammer"]:
                raise ValueError("sledgehammer must be a standalone command without parameters")
    return body
