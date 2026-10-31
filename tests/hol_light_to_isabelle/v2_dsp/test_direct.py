import copy
from contextlib import redirect_stdout
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from eval.pipeline.hol_light_to_isabelle.common import RESULTS_DIR, read_jsonl, repo_path, sha256, write_jsonl
from eval.pipeline.hol_light_to_isabelle.extract_hol_light import extract_records
from eval.pipeline.hol_light_to_isabelle.v2_dsp.export_dsp import export_inputs, export_record
from eval.pipeline.hol_light_to_isabelle.v2_dsp.generate_sketch import generate_sketches
from eval.pipeline.hol_light_to_isabelle.v2_dsp.direct_sketch_prompt import build_direct_sketch_prompt
from eval.pipeline.hol_light_to_isabelle.v2_dsp.input_contract import align_samples, input_metadata, output_path, validate_artifacts
from eval.pipeline.inference.config import resolve_config
from inference.fixtures import fake_vllm

MODULE = "eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp."
MODE = "hol-light-proof"


class DirectTests(unittest.TestCase):
    def setUp(self):
        self.record = extract_records(topic="circle_average", target_key="circleAverage_center_independent")[0]
        base = repo_path(RESULTS_DIR)
        base.mkdir(parents=True, exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(prefix="direct-mode-", dir=base)
        self.addCleanup(self.temp.cleanup)
        self.path = Path(self.temp.name)

    def test_direct_prompt_uses_source_proof_and_required_masked_reference_without_draft(self):
        raw = {**self.record, "draft": "DRAFT_SECRET", "draft_model": {"model": "DRAFT_MODEL_SECRET"},
               "informal_proof": "INFORMAL_SECRET", "isabelle_reference_proof": "COMPLETED_TARGET_SECRET"}
        row = export_record(raw, sketch_source=MODE)
        self.assertNotIn("draft", row)
        self.assertNotIn("draft_model", row)
        self.assertNotIn("informal_proof", row)
        self.assertFalse(row["draft_used"])
        prompt = build_direct_sketch_prompt(row)
        for field in ("hol_light_statement", "hol_light_proof", "hol_light_reference_context", "isabelle_statement"):
            self.assertIn(self.record[field], prompt.user_prompt)
        for secret in ("DRAFT_SECRET", "DRAFT_MODEL_SECRET", "INFORMAL_SECRET", "COMPLETED_TARGET_SECRET"):
            self.assertNotIn(secret, prompt.user_prompt + prompt.system_prompt)
        self.assertIn("Isabelle2026", prompt.system_prompt)

    def test_direct_mode_requires_all_source_fields_and_masking(self):
        for field in ("hol_light_statement", "hol_light_proof", "hol_light_reference_context"):
            with self.subTest(field=field), self.assertRaises(ValueError):
                export_record({**self.record, field: ""}, sketch_source=MODE)
        raw = copy.deepcopy(self.record)
        raw["hol_light_reference_context"] += "\nlet leaked_proof = prove (`T`, ACCEPT_TAC TRUTH);;"
        with self.assertRaisesRegex(ValueError, "contains proof"):
            export_record(raw, sketch_source=MODE)

    def test_direct_generation_calls_only_sketch_and_invalidates_actual_source_changes(self):
        source, output = self.path / "records.jsonl", self.path / "sketches.jsonl"
        write_jsonl(source, [self.record])
        with patch(MODULE + "generate_sketch.call_draft_model", return_value="by simp") as sketch, patch(
                "eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.generate_draft.generate_drafts") as draft:
            options = dict(input_path=source, output_path=output, sketch_source=MODE)
            self.assertEqual(1, generate_sketches(**options))
            self.assertEqual(0, generate_sketches(**options))
            changed = {**self.record, "hol_light_proof": self.record["hol_light_proof"] + " (* changed *)"}
            write_jsonl(source, [changed])
            self.assertEqual(1, generate_sketches(**options))
            changed = copy.deepcopy(changed)
            changed["hol_light_reference_context"] += "\n(* source reference revision *)"
            changed["metadata"]["hol_light_stmt_sha256"] = sha256(changed["hol_light_reference_context"])
            write_jsonl(source, [changed])
            self.assertEqual(1, generate_sketches(**options))
            self.assertEqual(1, generate_sketches(**options, model="different-model"))
            draft.assert_not_called()
        self.assertEqual(4, sketch.call_count)
        self.assertTrue(all("draft" not in row and row["sketch_source"] == MODE for row in read_jsonl(output)))
        self.assertNotIn("system_prompt", read_jsonl(output)[0])

    def test_incompatible_mode_or_pisa_output_file_is_rejected_even_without_resume(self):
        source, output = self.path / "records.jsonl", self.path / "sketches.jsonl"
        write_jsonl(source, [self.record])
        for old in ({**self.record, "pipeline": "v2-dsp", "schema_version": "hol_light_to_isabelle_dsp_v1"},
                    export_record({**self.record, "draft": "saved draft"})):
            write_jsonl(output, [old])
            with self.subTest(schema=old["schema_version"]), self.assertRaisesRegex(ValueError, "incompatible"):
                generate_sketches(input_path=source, output_path=output, sketch_source=MODE, resume=False)

    def test_source_changes_make_a_saved_direct_sketch_stale_and_keep_denominator(self):
        row = {**export_record(self.record, sketch_source=MODE), "sample_idx": 0, "isabelle_sketch": "by simp"}
        changed = {**self.record, "hol_light_proof": "changed actual proof"}
        rows = align_samples([row], [changed], 2, mode=MODE)
        self.assertEqual(2, len(rows))
        self.assertTrue(all(r["failure_category"] == "missing_sketch" for r in rows))

    def test_direct_default_output_does_not_invent_a_draft_model(self):
        qwen = resolve_config("eval/configs/inference/qwen_vllm.example.json", dry_run=True)
        path = output_path(None, results_dir=RESULTS_DIR, filename="sketches.jsonl", mode=MODE,
                           config=qwen, records=[self.record])
        self.assertIn("direct", path)
        self.assertIn("qwen_vllm", path)
        self.assertNotIn("api_draft", path)

    def test_both_dataset_clis_preview_direct_mode_without_native_or_draft_calls(self):
        from eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.extract_hol_light import extract_records as hundred
        records = [("babel_formal_pipeline", self.record),
                   ("hundred_theorems_pipeline", hundred(topic="030_the_ballot_problem", target_key="all_countings")[0])]
        for dataset, record in records:
            source = self.path / (dataset + ".jsonl")
            write_jsonl(source, [record])
            for module, extra in (("run", ["--config", "not-installed.local.json"]), ("generate_sketch", [])):
                command = [sys.executable, "-B", "-m", "eval.pipeline.hol_light_to_isabelle." + dataset + ".v2_dsp." + module,
                           "--sketch-source", MODE, "--records", str(source), "--dry-run", *extra]
                run = subprocess.run(command, text=True, capture_output=True, check=True, timeout=30)
                preview = json.loads(run.stdout)
                self.assertEqual(MODE, preview["sketch_source"])
                self.assertIn(record["hol_light_proof"], preview["user_prompt"])
                if dataset.startswith("hundred"):
                    self.assertTrue(preview["prompt_version"].startswith("hundred_theorems"))

    def test_direct_vllm_measures_the_complete_prompt_and_discards_reasoning(self):
        source, output = self.path / "records.jsonl", self.path / "sketches.jsonl"
        write_jsonl(source, [self.record])
        with fake_vllm(self.path) as server:
            server["content"] = "by simp"
            generate_sketches(input_path=source, output_path=output, sketch_source=MODE,
                              llm_config=server["profile_path"])
            tokens = [payload for url, payload in server["calls"] if url == "/tokenize"]
            self.assertEqual(1, len(tokens))
            self.assertIn(self.record["hol_light_reference_context"], tokens[0]["messages"][1]["content"])
            server["token_count"] = 1000000
            generate_sketches(input_path=source, output_path=output, sketch_source=MODE,
                              llm_config=server["profile_path"], resume=False)
            self.assertEqual(1, len([url for url, _ in server["calls"] if url.endswith("/chat/completions")]))
        self.assertTrue(read_jsonl(output)[0]["sketch_error"])
        self.assertNotIn("HIDDEN_REASONING_MARKER", output.read_text())


    def test_stale_saved_sketch_fingerprint_cannot_be_silently_relabelled(self):
        row = export_record(self.record, sketch_source=MODE)
        row["sketch_fingerprint"] = "saved"
        row["hol_light_proof"] += " changed source"
        with self.assertRaisesRegex(ValueError, "stale saved Sketch"):
            input_metadata(row, MODE)

    def test_failed_native_gate_makes_no_model_call_and_keeps_all_samples(self):
        from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.run_babel import main
        from v2_dsp.test_checker import BACKEND
        source, output = self.path / "records.jsonl", self.path / "verified.jsonl"
        write_jsonl(source, [self.record])
        args = ["runner", "--config", "eval/configs/hol_light_to_isabelle/v2_dsp.example.json",
                "--sketch-source", MODE, "--records", str(source), "--samples", "2",
                "--dsp-output", str(self.path / "inputs.jsonl"), "--sketch-output", str(self.path / "sketches.jsonl"),
                "--prove-output", str(self.path / "prove.jsonl"), "--output", str(output)]
        with patch.object(sys, "argv", args), patch(MODULE + "runtime.DspConfig.metadata", return_value=BACKEND), patch(
                MODULE + "run_babel.preflight", return_value={"ok": False, "baseline_ok": True}) as gate, patch(
                MODULE + "generate_sketch.call_draft_model") as model, redirect_stdout(io.StringIO()):
            main()
        self.assertTrue(gate.call_args.kwargs["controls"])
        model.assert_not_called()
        rows = read_jsonl(output)
        self.assertEqual(2, len(rows))
        self.assertTrue(all(not row["verified"] for row in rows))
        self.assertTrue(all(row["failure_category"] == "capability_error" for row in rows))


    def test_direct_sketch_search_and_replay_handoff_for_both_datasets(self):
        from v2_dsp.test_checker import BACKEND, CONFIG, FakeNative
        from eval.pipeline.hol_light_to_isabelle.v2_dsp.prove import prove_sketches
        from eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.extract_hol_light import extract_records as hundred
        for raw in (self.record, hundred(topic="030_the_ballot_problem", target_key="all_countings")[0]):
            with self.subTest(source=raw["source"]), redirect_stdout(io.StringIO()):
                prefix = raw["source"]
                source, exported, sketches, verified = [self.path / (prefix + name + ".jsonl")
                                                        for name in ("raw", "export", "sketch", "verified")]
                write_jsonl(source, [raw])
                rows = export_inputs(input_path=source, output_path=exported, sketch_source=MODE,
                                     expected_source=raw["source"])
                with patch(MODULE + "generate_sketch.call_draft_model", return_value="by simp"):
                    generate_sketches(input_path=exported, output_path=sketches, sketch_source=MODE,
                                      expected_source=raw["source"], samples=2)
                with patch(MODULE + "runtime.DspConfig.metadata", return_value=BACKEND), patch(
                        MODULE + "checker.NativeSearch", FakeNative):
                    result = prove_sketches(config=CONFIG, input_path=sketches, output_path=verified,
                        prove_output=None, expected=rows, expected_samples=2, sketch_source=MODE,
                        expected_source=raw["source"], results_dir=str(self.path))
                self.assertEqual(2, len(result))
                self.assertTrue(all(row["verified"] for row in result), [r.get("verify_error") for r in result])
                self.assertTrue(all(row["draft_used"] is False and "draft" not in row for row in result))


if __name__ == "__main__":
    unittest.main()
