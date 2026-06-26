# Eval

LLM translation and verification pipeline across 4 ITPs (Lean 4, Rocq, Isabelle, HOL Light).

## Directory Layout

```
eval/
├── .env               # API keys (not committed)
├── pipeline/              # implementation package
│   ├── config.py          # model list, prover list, paths
│   ├── translate.py       # synchronous LLM API dispatch (Claude, GPT, Gemini, OpenRouter)
│   ├── batch.py           # batch submit/poll per provider
│   ├── verify.py          # ITP verification via itpeval
│   ├── translation/       # ITP-to-ITP translation eval
│   │   ├── data.py        # load translation pairs from eval JSON
│   │   ├── prompt.py      # prompt builder
│   │   ├── run.py         # synchronous eval loop (debugging / small runs)
│   │   ├── batch_run.py   # batch pipeline: submit + collect
│   │   └── verify_generated.py  # verify pre-generated JSONL files in place
│   ├── cycle/             # multicycle NL↔ITP consistency experiment
│   │   ├── run.py         # cycle generation (NL→ITP→NL→ITP)
│   │   └── verify.py      # cycle verification
│   └── beq/               # bidirectional equivalence checking
│       ├── beq.py         # BEq implementation (extraction and tactic checks)
│       └── beq_check.py   # BEq runner: apply BEq to verified JSONL files
├── data/
│   ├── stmts.json     # 1,560 sorry-stripped theorem statements (390 theorems × 4 ITPs)
│   ├── proofs.json    # 296 full proofs (74 theorems × 4 ITPs)
│   └── minif2f_nl4itp.jsonl   # 483 MiniF2F records (NL + all 4 ITP stmts; cycle100 flag on 100)
└── results/            # local generated outputs
    ├── generated/      # raw model generations (JSONL per model)
    ├── verified/       # native ITP verification outputs (JSONL per model)
    ├── batch_jobs/     # batch job state/checkpoints
    └── cycle/          # multicycle consistency experiment outputs
        ├── cycle1/     # NL → Lean4 → NL → Lean4
        └── cycle2/     # NL → 4 ITPs → NL → 4 ITPs
```

## Setup

### API keys

Create `eval/.env`:

```
ANTHROPIC_API_KEY=...
OPENAI_API_KEY=...
GEMINI_API_KEY=...
OPENROUTER_API_KEY=...   # for DeepSeek and Qwen via OpenRouter
```

### ITP toolchains

The `collect` step runs actual ITP verifiers locally. Install them before collecting:

**macOS:**
```bash
cd itpeval
./bin/bootstrap-macos.sh
./bin/itpeval install lean4 rocq isabelle hol-light
```

**Linux:**
```bash
cd itpeval
./bin/bootstrap-system.sh
./bin/itpeval install lean4 rocq isabelle hol-light
```

Smoke-test with:
```bash
./bin/itpeval check lean4 rocq isabelle hol-light
```

### Python dependencies

```bash
pip install anthropic openai google-genai python-dotenv
```

## Data

Two flat JSON arrays, one record per (theorem, prover) pair:

| File | Content |
|---|---|
| `data/stmts.json` | Sorry-stripped theorem statements (no proof body) |
| `data/proofs.json` | Full proof files |

Record schema:

```json
{
  "theorem_id":  1,
  "title":       "circle_average",
  "source":      "babel-formal",
  "tier":        "a",
  "prover":      "lean4",
  "content":     "<full file text>"
}
```

`theorem_id` is globally unique (1–390). Only theorems in the 4-way intersection (all 4 ITPs) are included.

**Eval scope** (4,680 directed pairs for stmts, 888 for proofs):

| Benchmark | Tier | Theorems | ITPs | Pairs |
|---|---|---|---|---|
| babel-formal | A | 16 | isabelle, lean4, rocq, hol-light | 192 |
| hundred-theorems | B | 58 | isabelle, lean4, rocq, hol-light | 696 |
| minif2f | B | 316 | isabelle, lean4, rocq, hol-light | 3,792 |

For each theorem with *n* ITP variants, all *n × (n−1)* directed pairs are generated.

## Models

Configured in `config.py`. Current primary models:

| Label | Provider | Batch API | Notes |
|---|---|---|---|
| `claude-sonnet-4-6` | Anthropic | Anthropic Message Batches (async, 50% off) | |
| `gpt-5.5` | OpenAI | OpenAI Batch API (async ≤24h, 50% off) | Uses `max_completion_tokens` |
| `gemini-3.1-pro-preview` | Google | Gemini Batch API via File API | API key only; no GCS required |
| `deepseek-v4-pro` | OpenRouter | Synchronous via `run.py` | `deepseek/deepseek-v4-pro` on OpenRouter |
| `qwen3-235b-a22b` | OpenRouter | Synchronous via `run.py` | `qwen/qwen3-235b-a22b` on OpenRouter |

## Translation Modes

- **`stmts`** — source is the sorry-stripped statement; model generates a full proof in the target ITP.
- **`proofs`** — source is a full proof file; model translates the proof (and any definitions) into the target ITP.

## Running Evals

### Batch pipeline (recommended for full runs)

**Step 1 — Submit** (can be run on any machine with API keys):

```bash
python3 -m eval.pipeline.translation.batch_run submit \
    --mode stmts \
    --sources babel-formal,hundred-theorems,minif2f \
    --models claude-sonnet-4-6,gpt-5.5,gemini-3.1-pro-preview
```

Creates `eval/results/batch_jobs/<timestamp>.json`. Claude, GPT, and Gemini submit async batch jobs and return once the provider job IDs are recorded. Gemini requests are chunked before submission to keep batch sizes manageable.

`submit` options:

| Flag | Default | Description |
|---|---|---|
| `--mode` | `proofs` | `stmts` or `proofs` |
| `--sources` | all | comma-separated benchmark names |
| `--models` | all in config | comma-separated model labels |
| `--ids` | all | comma-separated theorem IDs (useful for small tests) |

**Step 2 — Collect** (requires ITP toolchains; run on a machine with them installed):

```bash
python3 -m eval.pipeline.translation.batch_run collect eval/results/batch_jobs/<timestamp>.json
```

- Polls Claude/GPT every 60 seconds until complete
- Verifies each generated proof by running it through the target ITP
- Writes results to `eval/results/batch_<mode>_<timestamp>.jsonl`
- Safe to re-run if interrupted — job file is updated in place as models complete

> **Running collect on a cluster**: The job file embeds all LLM responses once polling is complete, so no API keys are needed for the collect step. Copy the job file to the cluster, install ITP toolchains, and run the collect command above.

### Synchronous pipeline (debugging / small runs)

```bash
python3 -m eval.pipeline.translation.run \
    --mode stmts \
    --sources babel-formal \
    --ids 1,2,3 \
    --model claude-sonnet-4-6 \
    --dry-run          # omit to actually call the API
```

`run.py` options:

| Flag | Default | Description |
|---|---|---|
| `--mode` | `proofs` | `stmts` or `proofs` |
| `--sources` | all | comma-separated benchmark names |
| `--model` | all | comma-separated model labels |
| `--src` / `--tgt` | all | filter to one source or target prover |
| `--ids` | all | comma-separated theorem IDs |
| `--subset` | — | path to `{source, theorem_id}` JSON subset file |
| `--max-src-chars` | — | skip pairs whose source exceeds N chars |
| `--k` | 1 | samples per pair (for pass@k) |
| `--temperature` | 0.0 | sampling temperature; use >0 with `--k > 1` |
| `--workers` | 1 | parallel translation workers (ThreadPoolExecutor) |
| `--no-verify` | off | generate without running ITP verification |
| `--resume` PATH | — | continue from existing JSONL, skip completed jobs |
| `--dry-run` | off | print prompts, skip API calls and verification |

## Output Format

Both pipelines write JSONL to `eval/results/`. Each line:

```json
{
  "theorem_id":   42,
  "title":        "circle_average",
  "source":       "babel-formal",
  "tier":         "a",
  "src_prover":   "lean4",
  "tgt_prover":   "isabelle",
  "model":        "claude-sonnet-4-6",
  "model_id":     "claude-sonnet-4-6",
  "mode":         "stmts",
  "generated":    "<translated proof>",
  "verified":     true,
  "verify_error": "",
  "verify_ms":    3240
}
```

`verified: true` means the generated proof compiled and type-checked in the target ITP. `verify_error` contains the ITP error output on failure, or `"timeout after 120s"` if the verifier exceeded the time limit.

## Verifying pre-generated files

If you have a JSONL from `run.py --no-verify` (or from a batch run that skipped verification), use `verify_generated.py` to verify the stored outputs against the actual ITPs:

```bash
python3 -m eval.pipeline.translation.verify_generated \
    eval/results/generated/proofs_claude-sonnet-4-6_20260426.jsonl \
    eval/results/generated/stmts_claude-sonnet-4-6_20260426.jsonl
```

Multiple files can be passed at once (including shell brace expansion):

```bash
python3 -m eval.pipeline.translation.verify_generated \
    eval/results/generated/{proofs,stmts}_{claude-sonnet-4-6,gpt-5.5}_*.jsonl
```

Output is written to `eval/results/verified/` with the same filename. A `.ckpt.jsonl` checkpoint is maintained alongside so runs can be safely interrupted and resumed.

`verify_generated.py` options:

| Flag | Default | Description |
|---|---|---|
| `--workers` | 8 | parallel verification workers |
| `--hol-light-timeout-s` | 300 | override per-entry HOL Light timeout in seconds |

> **Note on HOL Light stmts**: HOL Light statement verification can be slow because each check loads the full `hol.ml` kernel (~60–90 s). Use `--hol-light-timeout-s` when those entries need a different timeout.

## Regeneration workflow

To regenerate translations for a specific subset of theorems (e.g., after fixing a prompt bug):

**Step 1 — Generate** (skip verification to get results quickly):

```bash
python3 -m eval.pipeline.translation.run \
    --mode proofs \
    --sources babel-formal \
    --ids 4,8,10,12 \
    --src isabelle \
    --model gpt-5.5 \
    --no-verify \
    --workers 4 \
    --resume eval/results/generated/regen_proofs_gpt-5.5.jsonl
```

**Step 2 — Verify** (on a machine with ITP toolchains):

```bash
python3 -m eval.pipeline.translation.verify_generated \
    eval/results/generated/regen_proofs_gpt-5.5.jsonl \
    --workers 8
```

**Step 3 — Merge** regen verified results back into the main result files by replacing the stale records (identified by `source`, `theorem_id`, `src_prover`, `tgt_prover`, `model`, `sample_idx`) with the regenerated ones, copying all original metadata fields unchanged and updating only `generated`, `verified`, `verify_error`, `verify_ms`.

## BEq equivalence checking

BEq (Bidirectional Extended Definitional Equivalence) checks whether verified translations preserve theorem meaning, adapting [Liu et al. (ICLR 2025)](https://openreview.net/forum?id=hUb2At2DsQ).

For each verified translation, BEq extracts the generated and reference theorem statements, then attempts to prove both forward (generated ⊢ reference) and backward (reference ⊢ generated) entailment. A translation passes BEq iff both directions succeed.

**Running BEq on verified results**:

```bash
python3 -m eval.pipeline.beq.beq_check \
    eval/results/verified/stmts_gpt-5.5_20260426.jsonl \
    --target lean4 \
    --workers 8
```

Output is written to `eval/results/beq/` with the same filename. Each record is augmented with:

| Field | Description |
|---|---|
| `beq` | `true` if both directions succeed |
| `beq_forward` / `beq_backward` | per-direction result |
| `beq_forward_tactic` / `beq_backward_tactic` | which tactic closed the goal |
| `beq_forward_ms` / `beq_backward_ms` | per-direction wall-clock time |
| `beq_forward_error` / `beq_backward_error` | error message on failure |
| `beq_extraction_error` | extraction/parsing error (if any) |

`beq_check.py` options:

| Flag | Default | Description |
|---|---|---|
| `--workers` | 8 | parallel workers (for non-Lean 4 entries) |
| `--source` | all | filter to a specific benchmark (e.g., `minif2f`) |
| `--target` | all | filter to a specific target prover (e.g., `lean4`) |

### Strategy per prover

**Lean 4 and Isabelle** use a *rename* approach: both theorems are placed in the same file, the assumed theorem is renamed to `stmt_assumed`, and the goal theorem's proof is replaced with a tactic check. Lean 4 checks each candidate independently, first using `exact?` and accepting it only when the suggestion references `stmt_assumed`, then trying deterministic normal tactics.

**Rocq and HOL Light** use an *axiom + extracted type* approach: the proposition type is extracted from each statement, the assumed proposition is declared as an axiom, and the goal proposition is proved using automation tactics.

### Automation tactics

Lean 4's deterministic checks are proxies for the BEq paper's LLM-sampled restricted transformation primitives. The normal Lean patterns are written to use `stmt_assumed`, avoiding standalone automation that can prove the goal independently. Other provers currently use broader prover-specific automation cascades.

| Prover | Tactics |
|---|---|
| **Lean 4 exact** | `exact?` |
| **Lean 4 normal** | `exact`, `apply`, `rw`, `intro`, `intros`, `constructor`, `ext`, `have`, `cases`, `use` |
| **Isabelle** | `rule`, `auto`, `simp`, `blast`, `force`, `fastforce`, `metis`, `meson`, `smt (verit)`, `smt (z3)`, `arith`, `linarith`, `presburger`, `normalization`, `argo`, `algebra` |
| **Rocq** | `exact`, `auto`, `eauto`, `tauto`, `intuition`, `firstorder`, `congruence`, `lia`, `lra`, `nra`, `ring`, `field_simplify`, `fourier`, `psatz` |
| **HOL Light** | `ACCEPT_TAC`, `MESON_TAC`, `ASM_MESON_TAC`, `SIMP_TAC`, `ASM_SIMP_TAC`, `REWRITE_TAC`, `ASM_REWRITE_TAC`, `ARITH_TAC`, `REAL_ARITH_TAC`, `INT_ARITH_TAC`, `NORM_TAC`, `MATCH_ACCEPT_TAC`, `NUMBER_TAC`, `ITAUT_TAC` |

## Multicycle consistency experiment

Tests how consistently a model round-trips between natural language and formal ITPs across two cycle types.

**Data**: `eval/data/minif2f_nl4itp.jsonl` — 483 MiniF2F records with fields:

```json
{
  "name":      "aime_1983_p1",
  "split":     "test",
  "nl":        "Let $x$, $y$ and $z$ all exceed $1$...",
  "lean4":     "<Lean 4 statement>",
  "isabelle":  "<Isabelle statement>",
  "rocq":      "<Rocq statement>",
  "hol_light": "<HOL Light statement or null>",
  "cycle100":  true
}
```

317 records have all 4 ITP statements; 166 are missing HOL Light.

100 records carry `"cycle100": true` — all 60 non-mathd test records
(amc, algebra, aime, induction, numbertheory) plus 40 randomly sampled mathd test records
(seed=42). This avoids the test split's ~62% mathd dominance while keeping full coverage
of the harder categories. Use `--cycle100` to filter to this subset.

**Cycle 1** — `NL → Lean4 → NL → Lean4`: tests whether Lean 4 formalizations are stable under NL round-trips.

**Cycle 2** — `NL → (all 4 ITPs) → NL → (all 4 ITPs)`: tests multi-ITP consistency; the model generates all four formalizations in a single call using section headers (`=== Lean 4 ===`, `=== Isabelle ===`, `=== Rocq ===`, `=== HOL Light ===`).

**Running**:

```bash
# Both cycles, all models, 1 worker per model
python3 -m eval.pipeline.cycle.run

# One cycle, specific model, parallel workers
python3 -m eval.pipeline.cycle.run \
    --cycle 1 \
    --model claude-sonnet-4-6 \
    --workers 4

# Only records with all 4 ITP stmts
python3 -m eval.pipeline.cycle.run --cycle 2 --all4
```

`cycle/run.py` options:

| Flag | Default | Description |
|---|---|---|
| `--cycle` | `both` | `1`, `2`, or `both` |
| `--model` | all | comma-separated model labels |
| `--workers` | 1 | parallel workers per model |
| `--max-tokens` | 4096 | max output tokens per API call |
| `--cycle100` | off | only the curated 100-record subset (records with `cycle100: true`) |
| `--split` | `both` | filter to `test`, `valid`, or `both` |
| `--all4` | off | only records with all 4 ITP statements |
| `--data` | default path | override input JSONL |

Output is written to `eval/results/cycle/cycle{1,2}/{model}.jsonl`, one record per theorem. Already-completed records are skipped on re-run (resume by default).

**Output schema — cycle 1**:

```json
{
  "name": "aime_1983_p1", "split": "test", "model": "claude-sonnet-4-6",
  "nl_ref": "...", "lean4_ref": "...",
  "step1_lean4": "...",  "step1_error": "", "step1_ms": 1234,
  "step2_nl":    "...",  "step2_error": "", "step2_ms": 987,
  "step3_lean4": "...",  "step3_error": "", "step3_ms": 1102
}
```

**Output schema — cycle 2**:

```json
{
  "name": "aime_1983_p1", "split": "test", "model": "claude-sonnet-4-6",
  "nl_ref": "...", "lean4_ref": "...", "isabelle_ref": "...", "rocq_ref": "...", "hol_light_ref": "...",
  "step1_lean4": "...", "step1_isabelle": "...", "step1_rocq": "...", "step1_hol_light": "...",
  "step1_raw": "...", "step1_error": "", "step1_ms": 3200,
  "step2_nl": "...", "step2_error": "", "step2_ms": 800,
  "step3_lean4": "...", "step3_isabelle": "...", "step3_rocq": "...", "step3_hol_light": "...",
  "step3_raw": "...", "step3_error": "", "step3_ms": 3100
}
```

## Adding new models

Models are registered in `eval/pipeline/config.py`:

```python
MODELS: list[dict] = [
    {"id": "gpt-5.5",                  "provider": "openai",      "label": "gpt-5.5"},
    {"id": "claude-sonnet-4-6",        "provider": "anthropic",   "label": "claude-sonnet-4-6"},
    {"id": "gemini-3.1-pro-preview",   "provider": "gemini",      "label": "gemini-3.1-pro-preview"},
    {"id": "deepseek/deepseek-v4-pro", "provider": "openrouter",  "label": "deepseek-v4-pro"},
    {"id": "qwen/qwen3-235b-a22b",     "provider": "openrouter",  "label": "qwen3-235b-a22b"},
]
```

Each entry has three fields:

| Field | Description |
|---|---|
| `id` | Model identifier as recognized by the provider's API. |
| `provider` | Dispatch key — determines which API client to use. |
| `label` | User-facing name for `--model` flag and output filenames. |

### Adding a model from a supported provider

Supported providers: `anthropic`, `openai`, `gemini`, `openrouter`, `groq`. To add a new model, append one line to `MODELS`:

```python
{"id": "claude-opus-4-1", "provider": "anthropic", "label": "claude-opus-4-1"},
```

Set the corresponding API key in `eval/.env` and use it:

```bash
python3 -m eval.pipeline.translation.run --model claude-opus-4-1 --sources babel-formal
python3 -m eval.pipeline.translation.batch_run submit --models claude-opus-4-1
```

Batch support (`batch_run.py`) is available for `anthropic`, `openai`, and `gemini`. The `openrouter` and `groq` providers are synchronous only — use `run.py` for those.

### Adding a new provider

**Step 1** — Add a dispatch branch in `eval/pipeline/translate.py`:

```python
elif provider == "my-provider":
    client = openai.OpenAI(
        api_key=os.environ["MY_PROVIDER_API_KEY"],
        base_url="https://api.my-provider.com/v1",
    )
    response = client.chat.completions.create(
        model=model_id,
        max_tokens=max_tokens,
        temperature=temperature,
        messages=[
            {"role": "system", "content": system_prompt},
            {"role": "user", "content": user_prompt},
        ],
    )
    text = response.choices[0].message.content
    if not text:
        raise ValueError(f"Empty response")
    return text
```

Most providers offer an OpenAI-compatible API (as shown above). For non-compatible APIs, adapt the client calls to the provider's SDK.

**Step 2** — Add the API key to `eval/.env`:

```
MY_PROVIDER_API_KEY=sk-...
```

**Step 3** — Register the model in `config.py`:

```python
{"id": "my-model-v1", "provider": "my-provider", "label": "my-model-v1"},
```

**Step 4 (optional)** — For batch support, implement `my_provider_submit()` and `my_provider_poll()` in `eval/pipeline/batch.py` and add them to the `submit()` / `poll()` dispatch. Each must follow the interface:

```python
def my_provider_submit(requests: list[dict], model_id: str, **kwargs) -> str:
    """Submit a batch. Return a batch ID string."""
    ...

def my_provider_poll(batch_id: str) -> tuple[str, dict[str, str] | None]:
    """Poll a batch. Return (status, results).
    status: 'in_progress' | 'completed' | 'failed'
    results: {custom_id: generated_text} when completed, else None.
    """
    ...
```
