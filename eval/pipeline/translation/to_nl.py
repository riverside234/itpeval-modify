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
    f"You are an expert mathematician and formal theorem prover, fluent in {src_name}. "
    "Given a formal source containing a specified target theorem and its proof, "
    "extract only the mathematical derivation needed to prove that target theorem. "
    "Convert the derivation into a sequence of small mathematical claims suitable "
    "for another theorem-proving model to formalize. "
    "Faithfully follow the proof strategy of the source proof. "
    "Do not invent an alternative proof. "
    "Do not summarize or translate unrelated lemmas from the surrounding source."
    )
    

    user = (
    f"TARGET THEOREM: {title}\n\n"

    "Convert only the proof of the TARGET THEOREM into a mathematical proof draft.\n\n"

    "Requirements:\n"
    "1. Read the source proof and identify the reasoning actually used to prove the target theorem.\n"
    "2. Ignore unrelated definitions, lemmas, and proofs in the surrounding source.\n"
    "3. If the target proof uses a previously established lemma, include only the mathematical "
    "fact from that lemma that is needed; do not reproduce its entire proof.\n"
    "4. Follow the same mathematical proof strategy as the source proof.\n"
    "5. Break the proof into small steps in logical order.\n"
    "6. Each step must contain exactly one principal mathematical claim.\n"
    "7. A claim may be an equation, inequality, proposition, quantified statement, "
    "case condition, set relation, or explicit witness.\n"
    "8. Preserve all intermediate facts necessary to reconstruct the target proof.\n"
    "9. Replace prover-specific tactics and commands with the mathematical facts they establish.\n"
    "10. Do not mention tactic names, automation, Isabelle syntax, or proof commands.\n"
    "11. Do not include explanatory prose when the mathematical claim can be stated directly.\n"
    "12. Do not refer to other draft steps using phrases such as 'by Step N' or 'using Step N'.\n"
    "13. The final step must state the target conclusion.\n"
    "14. Output only the numbered mathematical proof steps.\n\n"

    "Output format:\n"
    "### Step 1:\n"
    "<one mathematical claim>\n\n"
    "### Step 2:\n"
    "<one mathematical claim>\n\n"
    "...\n\n"

    f"=== FORMAL SOURCE ===\n"
    f"{source_content.strip()}\n"
    f"=== END FORMAL SOURCE ===\n\n"

    f"=== PROOF DRAFT FOR {title} ===\n"
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
