# Qwen inference for ITPEval

This adds local `Qwen/Qwen3.8-27B` inference for Draft and Sketch in both
Babel Formal and Hundred Theorems. The existing GPT-5.6 Terra API path is the
default. Both Isabelle verification pipelines use the same inference adapter.

The Python 3.12 server runs in a separate conda prefix, `vllm/env/`. The Python 3.10 ITPEval
environment sends HTTP requests to it; it does not import vLLM or PyTorch.
The `vllm/` directory contains scripts and deliberately has no `__init__.py`.

## Prepare the server environment on the Linux lab machine

Run from the repository root:

```bash
cd /data/not_backed_up/yxu209/ITPEval
source vllm/env_vars.sh

conda env create --prefix "$PWD/vllm/env" --file vllm/environment.yml
"$PWD/vllm/env/bin/python" -m pip install -r requirements-vllm.txt
"$PWD/vllm/env/bin/python" -m pip check
nvidia-smi
```

The explicit prefix keeps this environment separate from ITPEval, DSP+, and
the existing BFS-Prover environment. Server caches, model downloads,
temporary files, and logs default under `ITPEval/vllm/` and are Git-ignored.

The root `requirements-vllm.txt` contains the server dependency pins.
`vllm/requirements.lock.txt` includes that same file for compatibility.
Use the root `requirements.txt` in the separate Python 3.10 main environment;
it installs the local project and its dependencies from `pyproject.toml`.

The dependency inputs are pinned to vLLM 0.32.0, Transformers 5.19.0, and
huggingface-hub 2.3.0. Transformers 5.19.0 satisfies the selected vLLM release's
published `>=5.16.1,<5.20.0` constraint. These are direct dependency pins,
not a complete transitive or GPU-validated lock. The launcher records the
installed packages in `vllm/logs/server_packages.txt`.
[Published vLLM dependencies](https://pypi.org/pypi/vllm/0.32.0/json),
[Transformers dependencies](https://pypi.org/pypi/transformers/5.19.0/json).

Inspect `vllm/server.example.json` before downloading. Its initial settings
are BF16, one GPU, concurrency 1, and a 65,536-token total context. Choose GPU
allocation, tensor parallelism, dtype, and context length for the actual lab
hardware. Model weights, KV cache, and runtime allocations all need memory.
The launch preflight reports GPU capabilities and total memory; successful
model initialization remains a separate acceptance check.

To customize, copy the example to `vllm/server.local.json` and supply
`--config vllm/server.local.json` to the download and launch commands below.
The local file is ignored by Git. Preserve an existing scheduler-provided
`CUDA_VISIBLE_DEVICES`; otherwise the example selects GPU 0.

## Download and start the server

The downloader pins checkpoint commit
`1d4bf0f2ff6012fd82039f2fa52739d0dd7c60c0` from
[Qwen/Qwen3.8-27B](https://huggingface.co/Qwen/Qwen3.8-27B/tree/1d4bf0f2ff6012fd82039f2fa52739d0dd7c60c0).
It records the revision, file sizes, and tokenizer/template hashes.
A different revision requires a fresh model directory.

```bash
"$PWD/vllm/env/bin/python" vllm/download_model.py
"$PWD/vllm/env/bin/python" vllm/download_model.py --check

bash vllm/launch_qwen.sh --preflight
bash vllm/launch_qwen.sh
```

The launcher uses the isolated interpreter explicitly, checks package pins,
CUDA, GPU count, and the checkpoint manifest, then executes the official vLLM
server. It refuses an occupied port. The server runs in the foreground; use
another terminal to inspect `vllm/logs/qwen_server.log` or stop this server
with Ctrl-C in its launching terminal.

Defaults: `http://127.0.0.1:30002/v1` and served model name
`Qwen/Qwen3.8-27B`. The BFS-Prover server uses a separate port, 30001.
Launching writes `vllm/logs/server_manifest.json` with the actual model,
tokenizer/template hashes, versions, precision, GPU, and launch settings.
If the host, port, model, revision, or manifest location changes, update the
corresponding client profile too.

The command uses text-only serving, the `qwen3` reasoning parser, and explicit
generation parameters. Qwen's supported template effort labels are `low`,
`medium`, and `xhigh`; its profile starts with thinking enabled at `medium`.
[Official Qwen serving recipe](https://recipes.vllm.ai/Qwen/Qwen3.8-27B).

Preview the launch command without CUDA, installed server dependencies,
model files, or file creation:

```bash
python vllm/serve.py --dry-run
```

## Check the running server from the ITPEval environment

Use the usual ITPEval conda environment, with Python 3.10 or newer:

```bash
python vllm/check_server.py --smoke
```

This checks `/v1/models`, `/version`, the model root and runtime manifest,
then generates a small text response. Local inference does not require
`OPENAI_API_KEY`. Profiles contain environment variable names for optional
authentication, never actual credentials.

Measure every selected real Draft prompt, including full references:

```bash
python vllm/check_server.py \
  --records eval/results/hol_light_to_isabelle_v2/babel_formal_v2_exact_name_records.jsonl \
  --stage draft \
  --output eval/results/hol_light_to_isabelle_v2/qwen_prompt_lengths.json

python vllm/check_server.py \
  --records eval/results/hol_light_to_isabelle_v2/hundred-theorems/hundred_theorems_v2_records.jsonl \
  --stage draft \
  --output eval/results/hol_light_to_isabelle_v2/hundred-theorems/qwen_prompt_lengths.json
```

With saved Drafts, use `--stage itpeval-sketch` or `--stage dsp-sketch` to
measure each exact Sketch prompt. These checks use the server tokenizer and
chat template, report the largest prompt and failures, and make no generation
requests unless `--smoke` is also supplied.

For every generation, input tokens plus the configured output budget must
fit `max_model_len`. The output budget includes Qwen thinking and final
content. The adapter rejects overflow and incomplete outputs; it does not
truncate mathematical context.

## Generate a Qwen Draft

The input record files are the existing extracted dataset files.

```bash
python -m eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.generate_draft \
  --expected-root /data/not_backed_up/yxu209/ITPEval \
  --input eval/results/hol_light_to_isabelle_v2/babel_formal_v2_exact_name_records.jsonl \
  --topic circle_average --target-key circleAverage_center_independent \
  --llm-config eval/configs/inference/qwen_vllm.example.json \
  --output eval/results/hol_light_to_isabelle_v2/qwen_single_drafts.jsonl
```

Add `--dry-run` to preview the prompt and resolved model settings without
contacting the server or creating outputs. Omit the topic/target filters
for a batch. For Hundred Theorems use
`eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.generate_draft`
and its extracted record path; for example, select
`030_the_ballot_problem/all_countings`.

## Run Sketch and verification

Use the same saved Draft in either verifier baseline:

```bash
python -m eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_itpeval.run \
  --expected-root /data/not_backed_up/yxu209/ITPEval \
  --drafts eval/results/hol_light_to_isabelle_v2/qwen_single_drafts.jsonl \
  --topic circle_average --target-key circleAverage_center_independent \
  --sketch-llm-config eval/configs/inference/qwen_vllm.example.json \
  --samples 1

python -m eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.run \
  --expected-root /data/not_backed_up/yxu209/ITPEval \
  --config eval/configs/hol_light_to_isabelle/v2_dsp.local.json \
  --drafts eval/results/hol_light_to_isabelle_v2/qwen_single_drafts.jsonl \
  --topic circle_average --target-key circleAverage_center_independent \
  --sketch-llm-config eval/configs/inference/qwen_vllm.example.json \
  --samples 1
```

Each runner performs its existing prover preflight before generating a
Sketch. Add `--dry-run` to preview without installed prover dependencies.
Both baselines keep their original proof contracts: ITPEval generates a
complete body; DSP generates an Isar outline and fills its gaps before replay.

For Hundred Theorems use the corresponding
`hundred_theorems_pipeline.v2_itpeval.run` or
`hundred_theorems_pipeline.v2_dsp.run` module and its saved Draft file.

Independent Sketch generators accept `--llm-config`. The legacy Babel
`run_babel` runner accepts both `--draft-llm-config` and
`--sketch-llm-config`. Explicit `--model`, `--reasoning-effort`, and
`--max-output-tokens` values override profile settings. The saved-Draft
runners use the existing `--sketch-model` and `--sketch-reasoning-effort`
override names.

## API and mixed configurations

| Draft | Sketch | Configuration |
|---|---|---|
| API | API | Existing commands; no inference profile required |
| Qwen | Qwen | Qwen profile for Draft and Sketch |
| API | Qwen | Generate the API Draft first; select Qwen for Sketch |
| Qwen | API | Use the saved Qwen Draft; omit the Sketch profile |

The default API settings remain GPT-5.6 Terra, medium for Draft, high for
Sketch, and 16,000 output tokens. The API branch keeps Responses input and
reasoning parameters. The Qwen branch uses Chat Completions and
`chat_template_kwargs`; GPT's `high` effort is rejected for Qwen.
[OpenAI reasoning guide](https://developers.openai.com/api/docs/guides/reasoning),
[vLLM server API](https://docs.vllm.ai/en/latest/serving/online_serving/openai_compatible_server/).

With no explicit output path, API/API paths stay as before. Qwen Drafts and
Qwen/Qwen Sketch stages use a `qwen_vllm/` subdirectory under the stage's
usual output directory. Mixed runs use `api_draft_qwen_sketch/` or
`qwen_draft_api_sketch/`. Explicit output flags override these defaults.
Use distinct explicit output paths for further experimental variants.

Results retain the original record schema and add `draft_response` or
`sketch_response` with token counts, finish reason, and context budget.
Model metadata records the chosen profile and runtime identity. Only final
visible content enters `draft`, `isabelle_proof`, or `isabelle_sketch`.
Reasoning fields, raw responses, and prompt text are excluded from saved
generation output. Empty finals, unfinished thinking, length stops, and
connection errors remain failed records; there is no automatic paid-API
fallback.

Resume identities include the provider, checkpoint, runtime, sampling,
thinking settings, limits, and prompt. Existing compatible API Drafts
remain reusable. Returning to an earlier cached configuration restores its
record as the latest selected result.

## Validation status

Run from the repository root:

```bash
python -m unittest discover -s tests/hol_light_to_isabelle -p 'test_*.py'
```

Tests use a fake HTTP model/tokenizer and mocked API responses. They cover
both datasets, both Sketch variants, mixed backends, cache separation,
content-only output, and server tooling. They do not establish Qwen proof
quality, actual GPU memory fit, or native Isabelle success.

Native acceptance on the lab machine still requires the smoke request,
largest-prompt checks, one target through both verification baselines, and
one Hundred Theorems target. Keep identical prompts and sample counts when
comparing models and report their different reasoning/token budgets.

## Native Isabelle2026 direct Sketch inputs

The DSP-style pipeline supports `--sketch-source hol-light-proof --records ...`
with `--sketch-llm-config eval/configs/inference/qwen_vllm.example.json`.
There is no Draft-model call. Measure complete direct prompts with:

~~~bash
python vllm/check_server.py \
  --llm-config eval/configs/inference/qwen_vllm.example.json \
  --stage dsp-sketch --sketch-source hol-light-proof \
  --records eval/results/hol_light_to_isabelle_v2/single_records.jsonl
~~~

See [native DSP lab setup and experiment commands](../eval/pipeline/hol_light_to_isabelle/babel_formal_pipeline/v2_dsp/README.md).
