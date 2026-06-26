from __future__ import annotations
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
EVAL_DIR = REPO_ROOT / "eval"

STMTS_JSON  = EVAL_DIR / "data" / "stmts.json"
PROOFS_JSON = EVAL_DIR / "data" / "proofs.json"
RESULTS_DIR       = EVAL_DIR / "results"
GENERATED_DIR     = RESULTS_DIR / "generated"
VERIFIED_DIR      = RESULTS_DIR / "verified"
BATCH_JOBS_DIR = RESULTS_DIR / "batch_jobs"

PROVERS = ["lean4", "rocq", "isabelle", "hol-light"]

PROVER_DISPLAY = {
    "lean4":     "Lean 4",
    "rocq":      "Rocq (Coq)",
    "isabelle":  "Isabelle/HOL",
    "hol-light": "HOL Light",
}

MODELS: list[dict] = [
    {"id": "gpt-5.5",                  "provider": "openai",      "label": "gpt-5.5"},
    {"id": "claude-sonnet-4-6",        "provider": "anthropic",   "label": "claude-sonnet-4-6"},
    {"id": "gemini-3.1-pro-preview",   "provider": "gemini",      "label": "gemini-3.1-pro-preview"},
    {"id": "deepseek/deepseek-v4-pro", "provider": "openrouter",  "label": "deepseek-v4-pro"},
    {"id": "qwen/qwen3-235b-a22b",     "provider": "openrouter",  "label": "qwen3-235b-a22b"},
]
