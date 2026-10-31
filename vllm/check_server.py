"""Check identity, run a text smoke request, or measure full dataset prompts."""

from __future__ import annotations

import argparse
import importlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))

from eval.pipeline.inference.client import generate_text, server_preflight, token_budget
from eval.pipeline.inference.config import resolve_config, repository_path


def record_prompt(record: dict, stage: str, sketch_source: str = "draft"):
    dataset = {"babel-formal":"babel_formal_pipeline","hundred-theorems":"hundred_theorems_pipeline"}.get(record.get("source"))
    if dataset is None:
        raise ValueError("unsupported dataset in prompt-length check")
    prefix = "eval.pipeline.hol_light_to_isabelle."+dataset
    if stage=="draft":
        return importlib.import_module(prefix+".prompt").build_draft_prompt(record)
    if stage=="dsp-sketch":
        record = importlib.import_module(prefix+".v2_dsp.export_dsp").export_record(record, sketch_source=sketch_source)
        if sketch_source == "hol-light-proof":
            return importlib.import_module(prefix+".v2_dsp.direct_sketch_prompt").build_direct_sketch_prompt(record)
        return importlib.import_module(prefix+".v2_dsp.sketch_prompt").build_sketch_prompt(record)
    return importlib.import_module(prefix+".v2_itpeval.sketch_prompt").build_sketch_prompt(record)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--llm-config",default="eval/configs/inference/qwen_vllm.example.json")
    parser.add_argument("--smoke",action="store_true",help="Generate a real text response after health checks.")
    parser.add_argument("--records",help="Measure every selected rendered prompt; makes no generation requests.")
    parser.add_argument("--stage",choices=("draft","itpeval-sketch","dsp-sketch"),default="draft")
    parser.add_argument("--sketch-source", choices=("draft", "hol-light-proof"), default="draft",
                        help="DSP Sketch input mode; direct mode measures the entire HOL Light proof and masked reference.")
    parser.add_argument("--topic")
    parser.add_argument("--target-key")
    parser.add_argument("--limit",type=int)
    parser.add_argument("--output",help="Optional JSON report under the ITPEval root.")
    args = parser.parse_args()
    config = resolve_config(args.llm_config)
    report = {"server":server_preflight(config),"llm_config":config.to_metadata()}
    failed = False
    if args.records:
        from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.common import latest_records
        records = latest_records(args.records,topic=args.topic,target_key=args.target_key,limit=args.limit)
        if not records:
            parser.error("no matching records")
        rows = []
        for record in records:
            row = {name:record[name] for name in ("source","theorem_id","topic","target_key")}
            try:
                prompt = record_prompt(record,args.stage,args.sketch_source)
                row["token_budget"] = token_budget(config,[
                    {"role":"system","content":prompt.system_prompt},
                    {"role":"user","content":prompt.user_prompt}])
            except ValueError as exc:
                row.update(error=str(exc),**getattr(exc,"metadata",{}))
                failed = True
            rows.append(row)
        report.update(records=len(rows),failed_records=sum("error" in row for row in rows),prompts=rows)
        report["largest_prompt"] = max(rows,key=lambda row:row.get("token_budget",{}).get("prompt_tokens",0))
    if args.smoke:
        result = generate_text(
            system_prompt="Return only the requested final answer.",
            user_prompt="Reply with exactly: vLLM ready",config=config)
        report.update(content=str(result),response=result.metadata)
    if args.output:
        path = repository_path(args.output)
        path.parent.mkdir(parents=True,exist_ok=True)
        path.write_text(json.dumps(report,indent=2,ensure_ascii=False)+"\n",encoding="utf-8")
    print(json.dumps(report,indent=2,ensure_ascii=True))
    if failed:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
