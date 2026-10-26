import importlib
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline import common as shared_common
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.isabelle_syntax import (
    inventory_isabelle_declarations, tokens as isabelle_tokens,
)
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.theory_context import validate_context
from eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline import (
    aligned_data, extract_hol_light, inventory, manifest,
)
from eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.common import (
    RESULTS_DIR, SOURCE, read_jsonl, repo_path, write_jsonl,
)
from eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.generate_draft import generate_drafts
from eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.hol_syntax import (
    inventory_hol_declarations, mask_reference, tokens as hol_tokens,
)
from eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.masking import mask_isabelle_reference
from eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.prompt import build_draft_prompt
from eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.v2_dsp.export_dsp import export_record, export_drafts
from eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.v2_dsp.generate_sketch import generate_sketches as dsp_sketches
from eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.v2_dsp.preflight import control_record
from eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.v2_dsp.prove import prove_sketches
from eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.v2_itpeval.generate_sketch import generate_sketches
from eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.v2_itpeval.verify_isabelle import verify_sketches

B = "eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline"
H = "eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline"


class DataTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rows = inventory.inventory_topics()
        cls.report = {}
        cls.records = extract_hol_light.extract_records(report=cls.report)

    def test_entire_aligned_cohort_is_audited(self):
        self.assertEqual(58, len(self.rows))
        self.assertFalse([row for row in self.rows if row["error"]])
        self.assertEqual(99, self.report["candidate_count"])
        self.assertEqual(99, len(self.records))
        self.assertFalse([row for row in self.report["file_groups"] if row["issues"]])
        self.assertEqual(len(self.records), len({shared_common.key(row) for row in self.records}))
        self.assertTrue(all(row["source"] == SOURCE for row in self.records))
        self.assertTrue(all(not row["semantic_alignment_verified"] for row in self.records))

    def test_all_references_are_masked_and_named_declarations_retained(self):
        for tid, _ in aligned_data.list_topics():
            with self.subTest(theorem_id=tid):
                topic = aligned_data.load_topic(tid)
                raw = aligned_data.raw_inputs(tid)[2]["content"]
                self.assertEqual(
                    [d.name for d in inventory_isabelle_declarations(raw)],
                    [d.name for d in inventory_isabelle_declarations(topic.isabelle_stmt_content)])
                self.assertFalse({t.text for t in isabelle_tokens(topic.isabelle_stmt_content)
                                  if t.kind == "word"} & {"by","proof","apply","oops"})
                self.assertFalse([t for t in hol_tokens(topic.hol_light_stmt_content)
                                  if t.kind == "word" and t.text == "prove"])
        for record in self.records:
            self.assertEqual("sorry", record["isabelle_theory_template"][slice(*record["isabelle_target_proof_span"])])
            self.assertNotIn("isabelle_proof", record)
            self.assertIn("raw_isabelle_stmt_sha256", record["metadata"])

    def test_empty_target_file_is_reported_without_inventing_a_pair(self):
        row = next(row for row in self.rows if row["theorem_id"] == 17)
        self.assertEqual(0, row["isabelle_stmts"])
        self.assertFalse(row["candidate_pairs"])

    def test_draft_prompt_uses_dataset_label_and_same_translation_contract(self):
        prompt = build_draft_prompt(self.records[0])
        self.assertIn("Hundred Theorems", prompt.user_prompt)
        self.assertNotIn("TARGET: Babel Formal", prompt.user_prompt)
        self.assertIn("HOL LIGHT TARGET PROOF TO TRANSLATE", prompt.user_prompt)
        self.assertIn("COMPLETE PROOF-MASKED HOL LIGHT REFERENCE FILE", prompt.user_prompt)
        self.assertIn("Do not force brevity", prompt.user_prompt)
        self.assertIn("hundred_theorems", prompt.version)

    def test_short_inline_and_private_proofs_are_repaired(self):
        raw = (
            'section \\<open>Title with by proof\\<close>\n'
            'theory Example imports Main begin\n'
            'lemma a [simp]: "True" ..\n'
            'private lemma b: "True" unfolding a by simp\n'
            'lemma c: "True"\n proof -\n have "True" by simp\n then show ?thesis by simp\n qed\n'
            'definition d where "d = True"\nend\n'
        )
        masked = mask_isabelle_reference(raw)
        declarations = inventory_isabelle_declarations(masked)
        self.assertEqual(["a","b","c"], [d.name for d in declarations])
        self.assertIn('definition d where "d = True"', masked)
        self.assertIn('private lemma b', masked)
        from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.sanitize_isabelle import sanitize_target
        for name in ("a","b","c"):
            target = sanitize_target(masked,name)
            self.assertEqual("sorry", masked[slice(*target.proof_span)])
        self.assertEqual(masked, mask_isabelle_reference(masked))

    def test_local_proofs_do_not_become_exported_theorems(self):
        q = chr(96)
        source = f"let local = prove({q}P{q}, MESON_TAC[]) in install local;;\nlet TOP = prove({q}Q{q}, ALL_TAC);;"
        self.assertEqual(["TOP"], [d.name for d in inventory_hol_declarations(source,masked=False)])
        masked = mask_reference(source)
        self.assertNotIn("MESON_TAC", masked)
        self.assertNotIn("ALL_TAC", masked)
        dynamic = "let RULE tm = prove(tm, SOME_TAC);;"
        self.assertNotIn("SOME_TAC", mask_reference(dynamic))

    def test_duplicate_and_case_ambiguous_names_are_excluded(self):
        q = chr(96)
        proof = inventory_hol_declarations(f"let A = prove({q}True{q}, ALL_TAC);;\nlet A = prove({q}True{q}, ALL_TAC);;",masked=False)
        masked = inventory_hol_declarations(f"let A = {q}True{q};;",masked=True)
        isa = inventory_isabelle_declarations('lemma a: "True"\n sorry\n')
        self.assertEqual([],inventory.match_pairs(proof,masked,isa))

    def test_renamed_manual_mappings_and_verified_policy(self):
        base = repo_path(RESULTS_DIR)
        base.mkdir(parents=True,exist_ok=True)
        with tempfile.TemporaryDirectory(dir=base) as folder:
            path = Path(folder)/"manifest.json"
            target = dict(topic="example",target_key="target",hol_light_target_name="SOURCE",
                          isabelle_target_name="target",status="verified",
                          semantic_alignment_verified=True,notes="Review fixture.")
            path.write_text(json.dumps(dict(source=SOURCE,direction="hol-light-to-isabelle",targets=[target])))
            selected = manifest.targets_for_topic("example",[],verified_only=True,manifest_path=path)
            self.assertEqual("SOURCE",selected[0].hol_light_target_name)
            target["semantic_alignment_verified"] = False
            path.write_text(json.dumps(dict(source=SOURCE,direction="hol-light-to-isabelle",targets=[target])))
            with self.assertRaisesRegex(ValueError,"requires semantic"):
                manifest.load_targets(path)


class StageTests(unittest.TestCase):
    def setUp(self):
        base = repo_path(RESULTS_DIR)
        base.mkdir(parents=True,exist_ok=True)
        self.folder = tempfile.TemporaryDirectory(dir=base)
        self.addCleanup(self.folder.cleanup)
        self.root = Path(self.folder.name)
        self.record = extract_hol_light.extract_records(
            topic="030_the_ballot_problem",target_key="all_countings")[0]

    def test_draft_sketch_and_itpeval_contract(self):
        parsed,drafts,sketches,verified = [self.root/name for name in ("records.jsonl","drafts.jsonl","sketches.jsonl","verified.jsonl")]
        write_jsonl(parsed,[self.record])
        with patch(B+".generate_draft.call_draft_model",
                   return_value="<think>private deliberation</think>### Step 1\nApply the counting argument.") as model:
            self.assertEqual(1,generate_drafts(input_path=parsed,output_path=drafts))
            self.assertEqual(0,generate_drafts(input_path=parsed,output_path=drafts))
            model.assert_called_once()
        saved = read_jsonl(drafts)[0]
        self.assertNotIn("private deliberation",saved["draft"])
        self.assertNotIn("system_prompt",saved)
        self.assertNotIn("user_prompt",saved)
        with patch(B+".v2_itpeval.generate_sketch.call_draft_model",return_value="by simp"):
            generate_sketches(input_path=drafts,output_path=sketches,samples=2)
        self.assertTrue(all("hundred_theorems" in r["sketch_prompt_version"] for r in read_jsonl(sketches)))
        run = SimpleNamespace(ok=True,stdout="",stderr="",duration_ms=1,returncode=0)
        with patch(B+".v2_itpeval.verify_isabelle.isabelle2024_runtime",return_value={"prefix":".","version":"Isabelle2024"}), patch(
                B+".v2_itpeval.verify_isabelle.compile_theory",return_value=run) as compile_mock:
            results = verify_sketches(input_path=sketches,output_path=verified,expected=[saved],expected_samples=2)
        self.assertEqual(2,len(results))
        self.assertTrue(all(r["verified"] for r in results))
        self.assertEqual(RESULTS_DIR,compile_mock.call_args.kwargs["results_dir"])

    def test_dsp_export_and_sketch_contract(self):
        draft = {**self.record,"draft":"### Step 1\nApply the counting argument.","draft_error":None}
        draft_path,export_path,sketch_path = [self.root/name for name in ("drafts.jsonl","export.jsonl","sketches.jsonl")]
        write_jsonl(draft_path,[draft])
        exported = export_drafts(input_path=draft_path,output_path=export_path)
        self.assertEqual(draft["draft"],exported[0]["informal_proof"])
        self.assertEqual(draft["isabelle_statement"],exported[0]["formal_statement"])
        with patch(B+".v2_dsp.generate_sketch.call_draft_model",
                   return_value="proof -\n  show ?thesis\n    sledgehammer\nqed"):
            dsp_sketches(input_path=export_path,output_path=sketch_path,samples=2)
        rows = read_jsonl(sketch_path)
        self.assertEqual(2,len(rows))
        self.assertTrue(all("hundred_theorems" in row["sketch_prompt_version"] for row in rows))
        self.assertTrue(all("sledgehammer" in row["isabelle_sketch"] for row in rows))

    def test_dsp_search_replay_uses_own_directory_with_fake_transport(self):
        # This fixture exercises transport/control flow; it does not prove mathematics.
        from v2_dsp.test_checker import FakeSession, CONFIG, BACKEND
        sketch = control_record("proof -\n  show True\n    sledgehammer\nqed")
        input_path = self.root/"sketches.jsonl"
        write_jsonl(input_path,[sketch])
        with patch(B+".v2_dsp.runtime.DspConfig.metadata",return_value=BACKEND), patch(
                B+".v2_dsp.checker.PisaSession",FakeSession):
            results = prove_sketches(
                config=CONFIG,input_path=input_path,output_path=self.root/"verified.jsonl",
                prove_output=self.root/"prove.jsonl")
        self.assertTrue(results[0]["verified"],results[0]["verify_error"])
        self.assertTrue(Path(results[0]["workdir"]).is_relative_to(repo_path(RESULTS_DIR)))
        # The checker intentionally retains server work artifacts; clean up only this fixture's directory.
        self.addCleanup(self._remove_fixture_workdir,Path(results[0]["workdir"]))

    @staticmethod
    def _remove_fixture_workdir(path):
        import shutil
        if not path.resolve().is_relative_to(repo_path(RESULTS_DIR)):
            raise ValueError("fixture path escaped dataset results")
        shutil.rmtree(path)

    def test_cross_dataset_inputs_are_rejected_before_model_calls(self):
        path = self.root/"wrong.jsonl"
        write_jsonl(path,[{**self.record,"source":"babel-formal","draft":"example"}])
        with patch(B+".generate_draft.call_draft_model") as model:
            with self.assertRaisesRegex(ValueError,"expected hundred-theorems"):
                generate_drafts(input_path=path,output_path=self.root/"drafts.jsonl")
            model.assert_not_called()
        with self.assertRaisesRegex(ValueError,"expected hundred-theorems"):
            export_drafts(input_path=path,output_path=self.root/"dsp.jsonl")

    def test_new_runners_dry_run_without_native_dependencies_or_api(self):
        path = self.root/"drafts.jsonl"
        write_jsonl(path,[{**self.record,"draft":"Same shared Draft.","draft_error":None}])
        for runner in ("v2_itpeval","v2_dsp"):
            args = [sys.executable,"-B","-m",H+"."+runner+".run","--drafts",str(path),"--dry-run"]
            if runner == "v2_dsp":
                args += ["--config","eval/configs/hol_light_to_isabelle/missing.local.json"]
            completed = subprocess.run(args,capture_output=True,text=True,check=True,timeout=30)
            prompt = json.loads(completed.stdout)
            self.assertEqual(1,prompt["selected_records"])
            self.assertIn("Same shared Draft.",prompt["user_prompt"])
            self.assertNotIn("RuntimeWarning",completed.stderr)
        self.assertEqual(["drafts.jsonl"],sorted(p.name for p in self.root.iterdir()))

    def test_old_and_new_babel_modules_share_the_same_implementation(self):
        for suffix in ("aligned_data","extract_hol_light","generate_draft",
                       "v2_itpeval.generate_sketch","v2_dsp.prove"):
            self.assertIs(importlib.import_module("eval.pipeline.hol_light_to_isabelle."+suffix),
                          importlib.import_module(B+"."+suffix))

    def test_extract_cli_writes_records_and_complete_coverage_report(self):
        output = self.root/"all_records.jsonl"
        completed = subprocess.run(
            [sys.executable,"-B","-m",H+".extract_hol_light",
             "--all-topics","--all-targets","--output",str(output)],
            capture_output=True,text=True,check=True,timeout=60)
        self.assertIn("Wrote 99",completed.stdout)
        self.assertEqual(99,len(read_jsonl(output)))
        report = json.loads(Path(str(output)+".coverage.json").read_text(encoding="utf-8"))
        self.assertEqual(58,report["selected_file_groups"])
        self.assertEqual(99,report["record_count"])
        self.assertFalse([row for row in report["file_groups"] if row["issues"]])

    def test_dsp_enables_background_admissions_after_theory_not_documentation(self):
        from v2_dsp.test_checker import FakeSession, CONFIG, BACKEND
        from eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.v2_dsp.checker import Checker
        from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.sanitize_isabelle import sanitize_target
        template = ('section \\<open>Documentation first\\<close>\\n'
                    'theory HeaderTest imports Main begin\\nlemma goal: "True"\\n sorry\\nend\\n')
        # Turn escaped fixture newlines into actual source line breaks.
        template = template.replace("\\n","\n")
        target = sanitize_target(template,"goal")
        record = export_record(dict(
            source=SOURCE,theorem_id=0,topic="fixture",target_key="goal",
            isabelle_target_name="goal",draft="True holds.",sample_idx=0,
            isabelle_theory_template=template,isabelle_statement=target.statement,
            isabelle_context_before_target=target.context_before_target,
            isabelle_proof_prefix=target.proof_prefix,
            isabelle_target_proof_span=list(target.proof_span)))
        record["isabelle_sketch"] = "by simp"
        with patch(B+".v2_dsp.checker.repo_path",return_value=self.root):
            result = Checker(CONFIG,session_factory=FakeSession).check(record,backend_metadata=BACKEND)
        self.assertTrue(result["verified"],result["verify_error"])
        commands = [step["command"] for step in result["step_results"]
                    if step["mode"] == "search_context"]
        theory = next(i for i,command in enumerate(commands) if command.startswith("theory"))
        admission = commands.index("declare [[quick_and_dirty = true]]")
        self.assertGreater(admission,theory)

    def test_all_new_entry_points_import_without_native_runtime(self):
        modules = ["inventory","manifest","extract_hol_light","generate_draft",
                   "v2_itpeval.generate_sketch","v2_itpeval.verify_isabelle","v2_itpeval.run",
                   "v2_dsp.export_dsp","v2_dsp.generate_sketch","v2_dsp.preflight","v2_dsp.prove","v2_dsp.run"]
        for namespace in (B,H):
            for suffix in modules:
                completed = subprocess.run([sys.executable,"-B","-m",namespace+"."+suffix,"--help"],
                                           capture_output=True,text=True,timeout=30)
                self.assertEqual(0,completed.returncode,completed.stderr)
                self.assertIn("--expected-root",completed.stdout)
                self.assertNotIn("RuntimeWarning",completed.stderr)


if __name__ == "__main__":
    unittest.main()
