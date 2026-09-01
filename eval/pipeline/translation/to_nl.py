from __future__ import annotations

import argparse
import json
from pathlib import Path

from eval.pipeline.config import PROOFS_JSON, PROVER_DISPLAY
from eval.pipeline.models import select_models
from eval.pipeline.translate import translate


def build_to_nl_prompt(src_prover: str, title: str, source_content: str):
    src_name = PROVER_DISPLAY[src_prover]
    system = (
    f"You are an expert mathematician and formal theorem prover with expertise in {src_name}. "
    "Your task is to convert a completed formal proof into an informal mathematical proof draft. "
    "The draft will later be used by another automated theorem prover to reconstruct the proof "
    "in a different formal language. "
    "\n\n"
    "You are given a formal proof that may contain theorem declarations, assumptions, local facts, "
    "definitions, intermediate lemmas, tactic invocations, rewriting steps, automation, and "
    "prover-specific syntax. "
    "\n\n"
    "Extract the mathematical reasoning carried out by the proof. "
    "Preserve the proof strategy and all mathematically important intermediate facts. "
    "Translate prover-specific proof operations into the mathematical claims that they establish. "
    "\n\n"
    "The output must be a sequence of explicit mathematical proof steps. "
    "Each step should contain one principal mathematical claim, such as an equation, inequality, "
    "logical implication, quantified proposition, set relation, case assumption, or witness. "
    "\n\n"
    "Do not invent a different proof. "
    "Do not omit intermediate facts that are necessary to reconstruct the argument. "
    "Do not mention tactic names, proof commands, automation procedures, or details of the source prover. "
    "Do not discuss how the formalization works. "
    "Do not output source-language code. "
    "\n\n"
    "Use ordinary mathematical notation and preserve variable names when possible. "
    "The output must be self-contained enough that another mathematical theorem prover can follow "
    "the sequence of claims without seeing the original formal proof."
    )
    
    user = (
    f"Convert the following {src_name} formal proof into a mathematical proof draft.\n\n"

    "Instructions:\n"
    "1. Identify the theorem or result being proved.\n"
    "2. Read the entire formal proof before producing the draft.\n"
    "3. Follow the same proof strategy used in the formal proof.\n"
    "4. Extract the important assumptions and intermediate mathematical results actually used.\n"
    "5. Break the reasoning into small steps in logical order.\n"
    "6. Each step should state one principal mathematical fact.\n"
    "7. Prefer explicit formulas, equations, inequalities, propositions, or witnesses.\n"
    "8. If a tactic or automation proves a fact, output the resulting mathematical fact rather "
    "than the tactic name.\n"
    "9. Preserve case splits, induction hypotheses, contradiction assumptions, auxiliary variables, "
    "and witnesses when they are mathematically necessary.\n"
    "10. Do not include unrelated declarations or lemmas unless they are used by this proof.\n"
    "11. Do not invent intermediate statements unsupported by the source proof.\n"
    "12. Do not output Isabelle syntax or commentary about Isabelle.\n"
    "\n"
    "Output format:\n"
    "### Step 1:\n"
    "<one mathematical claim>\n\n"
    "### Step 2:\n"
    "<one mathematical claim>\n\n"
    "### Step 3:\n"
    "<one mathematical claim>\n\n"
    "Continue until the final theorem follows.\n"
    "\n"
    "The final step should state the conclusion being proved.\n"
    "\n"
    "If the proof is short, output only the necessary steps. "
    "If the proof is long, include all important intermediate claims but omit routine syntactic operations.\n"
    "\n"
    f"=== {src_name} FORMAL PROOF ===\n"
    f"{source_content.strip()}\n"
    f"=== END FORMAL PROOF ===\n\n"
    "Now produce the mathematical proof draft.\n\n"
    "### Step 1:\n"
    ) 
 
    return system, user


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", default="minif2f")
    parser.add_argument("--src", default="isabelle")
    parser.add_argument("--ids", required=True)
    parser.add_argument("--model", required=True)
    parser.add_argument(
        "--output",
        default="eval/results/isabelle_to_nl.jsonl",
    )
    args = parser.parse_args()

    theorem_ids = {int(x) for x in args.ids.split(",")}
    
    records = json.loads(Path(PROOFS_JSON).read_text())
    records = [
        r for r in records
        if r["source"] == args.source
        and r["prover"] == args.src
        and r["theorem_id"] in theorem_ids
    ]

    models = select_models(args.model)
    if len(models) != 1:
        raise ValueError("Please specify exactly one model")

    model_cfg = models[0]

    output_path = Path(args.output)
    output_path.parent.mkdir(parents=True, exist_ok=True)

    print(f"{len(records)} records")

    with output_path.open("w", encoding="utf-8") as f:
        for record in records:
            system, user = build_to_nl_prompt(
                src_prover=args.src,
                title=record["title"],
                source_content=record["content"],
            )

            nl = translate(
                system_prompt=system,
                user_prompt=user,
                model_cfg=model_cfg,
                temperature=0.0,
                max_tokens=8096,
            )

            result = {
                "theorem_id": record["theorem_id"],
                "title": record["title"],
                "source": record["source"],
                "src_prover": args.src,
                "model": model_cfg["label"],
                "formal_proof": record["content"],
                "natural_language": nl,
            }

            f.write(json.dumps(result, ensure_ascii=False) + "\n")
            f.flush()

            print(
                f'{record["theorem_id"]}: '
                f'{args.src} -> NL OK'
            )

    print(f"Done: {output_path}")


if __name__ == "__main__":
    main()
