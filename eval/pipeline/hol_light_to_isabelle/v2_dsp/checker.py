"""Babel-specific adaptation of original DSP's ordered tactic/hammer checker.

Search order derives from albertqjiang/draft_sketch_prove, commit 647aa65.
Copyright Sean Welleck, Albert Q. Jiang, Jin Peng Zhou and others.
See UPSTREAM_LICENSE.txt. PISA communication and replay are implemented here.
"""

from __future__ import annotations

import tempfile
import time
from pathlib import Path

from eval.pipeline.hol_light_to_isabelle.common import RESULTS_DIR, public_record, repo_path
from eval.pipeline.hol_light_to_isabelle.theory_context import (
    input_metadata, normalize_body, tokens, validate_context,
)
from eval.pipeline.hol_light_to_isabelle.v2_dsp.runtime import DspConfig, PisaSession


CHECKER_VERSION = "babel_formal_v2_dsp_checker_p1"
HEURISTICS = (
    "by auto", "by simp", "by blast", "by fastforce", "by force", "by eval",
    "by presburger", "by sos", "by arith", "by linarith", "by (auto simp: field_simps)",
)


class ProofFailure(RuntimeError):
    def __init__(self, category: str, message: str):
        super().__init__(message)
        self.category = category


class Checker:
    def __init__(self, config: DspConfig, *, session_factory=None):
        self.config = config
        self.session_factory = session_factory or PisaSession
        self.steps: list[dict] = []
        self.serial = 0

    def _attempt(self, session, command: str, state: str, mode: str,
                 *, hammer: bool = False) -> tuple[str, str]:
        self.serial += 1
        name = f"v2_{mode}_{self.serial}"
        started = time.monotonic()
        row = {"mode": mode, "command": command, "source_state": state, "new_state": name}
        try:
            output = session.step(command, state, name, hammer=hammer)
            row.update(success=True, observation=output[:16000])
            return name, output
        except Exception as exc:
            row.update(success=False, error=f"{type(exc).__name__}: {exc}")
            raise
        finally:
            row["duration_seconds"] = round(time.monotonic() - started, 3)
            self.steps.append(row)

    def _prepare(self, session, context, record: dict, mode: str) -> str:
        state = "default"
        commands = session.parse(context.prefix)
        for index, command in enumerate(commands):
            state, _ = self._attempt(session, command, state, mode + "_context")
            if index == 0:
                state, _ = self._attempt(
                    session, "declare [[quick_and_dirty = true]]", state, mode + "_context")
        state, _ = self._attempt(
            session, "declare [[quick_and_dirty = false]]", state, mode + "_context")
        for command in session.parse(context.statement + "\n" + context.proof_prefix):
            state, _ = self._attempt(session, command, state, mode + "_target")
        if session.finished(state):
            raise ProofFailure("context_error", "oracle declaration did not open a target proof")
        return state

    def _fill(self, session, sketch: str, state: str) -> tuple[str, str]:
        replacements = []
        for command in session.parse(sketch):
            items = tokens(command)
            gaps = [item for item in items if item.kind == "word" and item.text == "sledgehammer"]
            if not gaps:
                try:
                    state, _ = self._attempt(session, command, state, "search")
                except RuntimeError as exc:
                    raise ProofFailure("sketch_step_failure", str(exc)) from exc
                continue
            if len(items) != 1 or len(gaps) != 1:
                raise ProofFailure("sketch_parse_error", "use a standalone sledgehammer command")
            selected = None
            for heuristic in HEURISTICS:
                try:
                    new, _ = self._attempt(session, heuristic, state, "heuristic")
                    selected, state = heuristic, new
                    break
                except RuntimeError:
                    continue
            if selected is None:
                try:
                    state, output = self._attempt(session, "normalhammer", state, "hammer",
                                                  hammer=True)
                except RuntimeError as exc:
                    raise ProofFailure("hammer_failure", str(exc)) from exc
                if "<hammer>" not in output:
                    raise ProofFailure("missing_reconstruction", "hammer returned no concrete method")
                selected = output.split("<hammer>", 1)[0].strip()
                try:
                    normalize_body(selected)
                except ValueError as exc:
                    raise ProofFailure("missing_reconstruction", str(exc)) from exc
            replacements.append(selected)
        markers = [item for item in tokens(sketch)
                   if item.kind == "word" and item.text == "sledgehammer"]
        if len(markers) != len(replacements):
            raise ProofFailure("sketch_parse_error", "PISA did not preserve all sketch gaps")
        filled = sketch
        for item, method in reversed(list(zip(markers, replacements))):
            filled = filled[:item.start] + method + filled[item.end:]
        return normalize_body(filled), state

    def check_context(self, record: dict, *, backend_metadata: dict | None = None) -> dict:
        context = validate_context(record)
        base = repo_path(RESULTS_DIR + "/v2-dsp/work")
        base.mkdir(parents=True, exist_ok=True)
        directory = Path(tempfile.mkdtemp(prefix="preflight-", dir=base))
        self.steps, self.serial = [], 0
        backend = backend_metadata or self.config.metadata()
        with self.session_factory(
            self.config, directory, context.theory_name, context.template,
            deadline=time.monotonic() + self.config.target_timeout_s,
        ) as session:
            self._prepare(session, context, record, "preflight")
        return {"baseline_ok": True, "workdir": str(directory),
                "backend_metadata": backend, **context.metadata}

    def check(self, record: dict, *, replay_only: bool = False,
              backend_metadata: dict | None = None) -> dict:
        result = {**public_record(record), "pipeline": "v2-dsp",
                  "checker_version": CHECKER_VERSION, "prove_success": False,
                  "replay_verified": False, "verified": False, "verify_error": "",
                  "failure_category": None}
        self.steps, self.serial = [], 0
        started = time.monotonic()
        stage = "input_error"
        try:
            if record.get("pipeline") != "v2-dsp":
                raise ValueError("input is not a v2-dsp record")
            if record.get("input_error") or record.get("sketch_error"):
                raise ProofFailure(record.get("failure_category") or "sketch_error",
                                   record.get("input_error") or record["sketch_error"])
            result.update(input_metadata(record))
            context = validate_context(record)
            proof = normalize_body(record.get("isabelle_proof" if replay_only else "isabelle_sketch", ""),
                                   allow_hammer=not replay_only)
            stage = "toolchain_error"
            result["backend_metadata"] = backend_metadata or self.config.metadata()
            base = repo_path(RESULTS_DIR + "/v2-dsp/work")
            base.mkdir(parents=True, exist_ok=True)
            directory = Path(tempfile.mkdtemp(prefix="target-", dir=base))
            result["workdir"] = str(directory)
            deadline = started + self.config.target_timeout_s
            with self.session_factory(
                self.config, directory, context.theory_name, context.template,
                deadline=deadline,
            ) as session:
                if not replay_only:
                    stage = "context_error"
                    state = self._prepare(session, context, record, "search")
                    stage = "sketch_step_failure"
                    proof, state = self._fill(session, proof, state)
                    if not session.finished(state):
                        raise ProofFailure("incomplete_proof", "sketch left the target proof open")
                    result["prove_success"] = True
                    result["isabelle_proof"] = proof
                else:
                    result["isabelle_proof"] = proof
                stage = "replay_failure"
                state = self._prepare(session, context, record, "replay")
                for command in session.parse(proof):
                    state, _ = self._attempt(session, command, state, "replay")
                if not session.finished(state):
                    raise ProofFailure("replay_failure", "completed proof left unresolved goals")
                for _ in range(context.depth):
                    state, _ = self._attempt(session, "end", state, "close_scope")
                result["prove_success"] = True
                result["replay_verified"] = result["verified"] = True
                result["replay_theory_path"] = str(directory / "replayed.thy")
                (directory / "replayed.thy").write_text(context.theory(proof), encoding="utf-8")
        except Exception as exc:
            result["verify_error"] = f"{type(exc).__name__}: {exc}"
            result["failure_category"] = (
                exc.category if isinstance(exc, ProofFailure) else
                "timeout" if isinstance(exc, (TimeoutError,)) else
                "rejected_proof" if isinstance(exc, ValueError) and stage == "input_error" else stage)
        result["step_results"] = self.steps
        result["verify_duration_seconds"] = round(time.monotonic() - started, 3)
        return result
