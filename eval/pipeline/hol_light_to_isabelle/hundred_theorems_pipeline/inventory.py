"""Inventory every aligned Hundred Theorems file and report alignment coverage."""

from __future__ import annotations

import argparse
from collections import Counter
import json

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.isabelle_syntax import inventory_isabelle_declarations
from .aligned_data import list_topics, load_topic
from .common import LAB_REPO_ROOT, SOURCE, repo_path, validate_layout
from .hol_syntax import inventory_hol_declarations


def match_pairs(proof, masked, isa) -> list[tuple[str,str,str]]:
    pc,mc,ic = (Counter(item.name for item in items) for items in (proof,masked,isa))
    source_fold = Counter(item.name.casefold() for item in proof)
    targets = {}
    for item in isa:
        targets.setdefault(item.name.casefold(),[]).append(item.name)
    statements = {item.name:" ".join(item.statement.split()) for item in masked if mc[item.name] == 1}
    result = []
    for item in proof:
        if pc[item.name] != 1 or mc[item.name] != 1 or source_fold[item.name.casefold()] != 1:
            continue
        if " ".join(item.statement.split()) != statements[item.name]:
            continue
        matches = targets.get(item.name.casefold(),[])
        if len(matches) != 1 or ic[matches[0]] != 1:
            continue
        name = matches[0]
        result.append((item.name,name,"exact_name_match" if item.name == name else "casefold_name_match"))
    return result


def inventory_topic(topic) -> dict:
    proof = inventory_hol_declarations(topic.hol_light_proof_content,masked=False)
    masked = inventory_hol_declarations(topic.hol_light_stmt_content,masked=True)
    isa = inventory_isabelle_declarations(topic.isabelle_stmt_content,topic=topic.topic)
    pairs = match_pairs(proof,masked,isa)
    source_names,target_names = {pair[0] for pair in pairs},{pair[1] for pair in pairs}
    duplicates = {}
    for label,items in (("hol_light_proofs",proof),("hol_light_stmts",masked),("isabelle_stmts",isa)):
        duplicates[label] = sorted(name for name,count in Counter(item.name for item in items).items() if count > 1)
    return {
        "source": SOURCE,"theorem_id":topic.theorem_id,"topic":topic.topic,
        "hol_light_proofs":len(proof),"hol_light_stmts":len(masked),"isabelle_stmts":len(isa),
        "exact_name_matches":[target for source,target,status in pairs if status == "exact_name_match"],
        "candidate_pairs":pairs,"duplicate_names":duplicates,
        "unmatched_hol_light":[item.name for item in proof if item.name not in source_names],
        "masked_hol_without_extracted_proof":[item.name for item in masked
                                            if item.name not in {d.name for d in proof}],
        "unmatched_isabelle":[item.name for item in isa if item.name not in target_names],
        "semantic_alignment_verified":False,"error":None,
    }


def inventory_topics(*, topic: str | None = None, theorem_id: int | None = None) -> list[dict]:
    result = []
    for tid,title in list_topics():
        if (topic is not None and title != topic) or (theorem_id is not None and tid != theorem_id):
            continue
        try:
            row = inventory_topic(load_topic(tid))
        except (ValueError,KeyError) as exc:
            row = {"source":SOURCE,"theorem_id":tid,"topic":title,"candidate_pairs":[],
                   "error":f"{type(exc).__name__}: {exc}"}
        result.append(row)
    if not result:
        raise ValueError("no matching Hundred Theorems file group")
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expected-root",help=f"Lab repo: {LAB_REPO_ROOT}")
    parser.add_argument("--all-topics",action="store_true")
    parser.add_argument("--topic")
    parser.add_argument("--id",type=int)
    parser.add_argument("--names",action="store_true")
    parser.add_argument("--json",action="store_true")
    parser.add_argument("--output",help="Optional detailed inventory JSON, inside the repository.")
    args = parser.parse_args()
    validate_layout(args.expected_root)
    if args.all_topics and (args.topic or args.id is not None):
        parser.error("choose --all-topics or --topic/--id")
    rows = inventory_topics(topic=args.topic,theorem_id=args.id)
    if args.output:
        path = repo_path(args.output)
        path.parent.mkdir(parents=True,exist_ok=True)
        path.write_text(json.dumps(rows,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
    if args.json:
        print(json.dumps(rows,ensure_ascii=True,indent=2))
        return
    for row in rows:
        if row["error"]:
            print(f'{row["theorem_id"]:2d} {row["topic"]}: ERROR {row["error"]}')
            continue
        print(f'{row["theorem_id"]:2d} {row["topic"]}: hol_light_proofs={row["hol_light_proofs"]} '
              f'hol_light_stmts={row["hol_light_stmts"]} isabelle_stmts={row["isabelle_stmts"]} '
              f'candidates={len(row["candidate_pairs"])}')
        if args.names:
            for source,target,status in row["candidate_pairs"]:
                print(f"  {source} -> {target} ({status})")
    print(f'Total candidate matches: {sum(len(row["candidate_pairs"]) for row in rows)}')


if __name__ == "__main__":
    main()
