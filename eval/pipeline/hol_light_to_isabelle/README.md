# HOL Light to Isabelle pipelines

Both stages now support selectable inference backends. Existing commands use
the GPT-5.6 Terra API defaults. Add `--llm-config
eval/configs/inference/qwen_vllm.example.json` to a standalone generator,
or `--sketch-llm-config` to a saved-Draft runner, for local Qwen inference.
The server uses its own `vllm/env/` conda prefix and keeps artifacts under
`vllm/`. See [Qwen setup and run commands](../../../vllm/README.md).
API/API, Qwen/Qwen, and mixed-stage default outputs are separated.

Each dataset has its own data preparation, prompts, manifests, and executable
stages. Each prepared record represents one HOL Light proof and its candidate
oracle Isabelle declaration.

```text
hol_light_to_isabelle/
├── babel_formal_pipeline/
│   ├── aligned_data.py, inventory.py, manifest.py, extract_hol_light.py
│   ├── prompt.py, generate_draft.py, sanitize_isabelle.py, theory_context.py
│   ├── manifests/babel_targets.json
│   ├── v2_itpeval/     # complete proof generation and Isabelle2024 checking
│   └── v2_dsp/         # Isar Sketch, DSP search, reconstruction, and replay
└── hundred_theorems_pipeline/
    ├── aligned_data.py, inventory.py, manifest.py, extract_hol_light.py
    ├── hol_syntax.py, masking.py
    ├── prompt.py, generate_draft.py, sanitize_isabelle.py, theory_context.py
    ├── manifests/hundred_targets.json
    ├── v2_itpeval/
    └── v2_dsp/
```

- [Babel Formal instructions](babel_formal_pipeline/README.md)
- [Hundred Theorems instructions](hundred_theorems_pipeline/README.md)

Both use the same Draft, oracle/context, model-content, sampling, resume,
verification, and DSP replay contracts. Hundred Theorems frontends reuse the
execution engines in the Babel package with explicit dataset parameters.
Changing a dataset does not require copying the prover implementation.

Babel's existing output paths remain under
`eval/results/hol_light_to_isabelle_v2/`. Hundred Theorems defaults to
`eval/results/hol_light_to_isabelle_v2/hundred-theorems/`, with separate
`v2-itpeval/` and `v2-dsp/` results and work directories. Source checks prevent
one dataset's records from entering the other's stage entry points.

The small Python modules at the original package paths are compatibility
aliases to `babel_formal_pipeline`. Existing scripts and saved Babel
records/Drafts remain usable. New scripts should use the dataset package:

```text
eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.<stage>
eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.<stage>
```

Each dataset's `v2_itpeval.run` and `v2_dsp.run` entry points accept saved
Drafts. The previous Babel `run_babel` command remains available.

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
transport tests are explicit fakes. Run native preflight in the configured lab
environment before generating the experiment batch.
