# HOL Light to Isabelle pipelines

Both stages now support selectable inference backends. Existing commands use
the gpt-6.1-terra API defaults. Add `--llm-config
eval/configs/inference/qwen_vllm.example.json` to a standalone generator,
or `--sketch-llm-config` to a saved-Draft runner, for local Qwen inference.
Start the server after `conda activate vllm` (Python 3.12); it keeps artifacts under
`vllm/`. See [Qwen setup and run commands](../../../vllm/README.md).
API/API, Qwen/Qwen, and mixed-stage default outputs are separated.

Each dataset has its own data preparation, prompts and executable
stages. Each prepared record represents one HOL Light proof and its candidate
oracle Isabelle declaration.

```text
hol_light_to_isabelle/
├── babel_formal_pipeline/
│   ├── aligned_data.py, inventory.py, manifest.py, extract_hol_light.py
│   ├── prompt.py, generate_draft.py, sanitize_isabelle.py, theory_context.py
│   ├── manifests/babel_targets.json
│   ├── v2_itpeval/     # complete proof generation and Isabelle2024 checking
│   ├── v2_dsp/         # Draft/direct Sketch and native Isabelle2026 (default)
│   └── v2_dsp_pisa/    # Original DSP/PISA/Isabelle2021 option
├── hundred_theorems_pipeline/
│   ├── aligned_data.py, inventory.py, manifest.py, extract_hol_light.py
│   ├── hol_syntax.py, masking.py
│   ├── prompt.py, generate_draft.py, sanitize_isabelle.py, theory_context.py
│   ├── manifests/hundred_targets.json
│   ├── v2_itpeval/
│   ├── v2_dsp/
│   └── v2_dsp_pisa/
└── most_match_pipeline/
    ├── aligned_data.py, inventory.py, context.py, extract_hol_light.py
    ├── prompt.py, generate_draft.py
    └── v2_dsp/         # bounded references; native Isabelle2026
```

- [Babel Formal instructions](babel_formal_pipeline/README.md)
- [Hundred Theorems instructions](hundred_theorems_pipeline/README.md)
- [Most-match instructions](most_match_pipeline/README.md) — 353 candidates, bounded model context, parallel native verification

Babel and Hundred Theorems use the same oracle/context, model-content, sampling, resume,
verification, and native/PISA completion contracts. Hundred Theorems frontends reuse the
execution engines in the Babel package with explicit dataset parameters.
Changing a dataset does not require copying the prover implementation.

Babel's existing output paths remain under
`eval/results/hol_light_to_isabelle_v2/`. Hundred Theorems defaults to
`eval/results/hol_light_to_isabelle_v2/hundred-theorems/`, with separate
`v2-itpeval/`, `v2-dsp-isabelle2026/` and `v2-dsp-pisa-isabelle2021/` results and work directories. Source checks prevent
one dataset's records from entering the other's stage entry points.

The small Python modules at the original package paths are compatibility
aliases to `babel_formal_pipeline`. Existing scripts and saved Babel
records/Drafts remain usable. Native 2026 and PISA 2021 configurations and artifacts are kept separate.
`v2_dsp/` is native; `v2_dsp_pisa/` preserves original DSP/PISA. Neither has a separate replay stage. New scripts should use the dataset package:

```text
eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.<stage>
eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.<stage>
```

Babel and Hundred Theorems `v2_itpeval.run` and `v2_dsp.run` entry points accept saved
Drafts. DSP also accepts `--sketch-source hol-light-proof --records ...`
for direct Sketch generation. See [native Isabelle2026 lab commands](babel_formal_pipeline/v2_dsp/README.md).
The previous Babel `run_babel` command remains available.

The current aligned data yields 163 Babel candidates and 99 Hundred Theorems
candidates. These are name-based alignments, not automatic semantic reviews.
Hundred Theorems supplies 58 aligned file groups in `eval/data`; this does not
mean 100 individual usable proof pairs. Its detailed coverage report records
unmatched declarations, ambiguous names, missing source proofs, and extraction
issues. Renamed correspondences can be added to its manifest after review.

Run tests from the ITPEval repository root:

```bash
python -m unittest discover -s tests/hol_light_to_isabelle -p 'test_*.py'
```

These tests require no API calls or native prover installation. DSP
adapter tests are explicit fakes. Run native preflight in the configured lab
environment before generating the experiment batch.

Babel and Hundred Theorems also have `v2_dsp_pisa/` frontends; see [PISA setup](babel_formal_pipeline/v2_dsp_pisa/README.md).


Most-match uses `eval/results/hol_light_to_isabelle_v2/most-match/` and
`eval/preflight_results/isabelle2026-most-match/`. Its Draft, direct Sketch and
saved-Draft Sketch prompts use bounded references while the native checker keeps
the complete preceding masked Isabelle context. It shares the checked native
prover implementation; it does not copy a new prover or add a replay stage.

Test only the new dataset with the shared preflight selector:

```bash
python -m eval.pipeline.hol_light_to_isabelle.v2_dsp.lab_preflight \
  --expected-root "$PWD" --dataset most-match --workers 60
```

Add `--all-targets` for every most-match candidate. Without it, the current snapshot
selects 65 representative contexts. `--dataset both` retains the original
Babel/Hundred cohort. Native DSP runners, Prove commands and lab preflights accept
`--workers 1..60`, `--threads-per-worker` and `--memory-per-worker-gb`; see the
[most-match parallel execution notes](most_match_pipeline/README.md#parallel-execution).
