"""Build the direct Sketch reference views and selection reports."""

from dataclasses import asdict, dataclass

from ..babel_formal_pipeline.common import fingerprint, key, sha256
from ..isabelle_references import proof_context, store_context
from ..most_match_pipeline.common import DATASET_ROOT, SOURCE as MOST_MATCH_SOURCE
from ..most_match_pipeline.context import (
    DEPENDENCY_CONTEXT_VERSION, identifiers, isabelle_snippets, selected_reference_proofs,
    source_snippets, validate_prompt_context,
)
from .contracts import ALIGNED_CAP_SETTINGS, ContextConfig, EXPANSION_SETTINGS, LOAD_SETTINGS, VERSION, context_arm
from .datasets import dataset_for
from .dependencies import imported_definitions, source_packages, walk
from .expansion import select_source_helpers
from .prompts import BUNDLE_DIGEST, BUNDLE_FIELD
from .selection import Selection
from .source_index import load_source
from . import target_facts


def full_reference_info(text, snippets):
    return {"budget_chars": None, "selected_chars": len(text), "sha256": sha256(text),
            "selected_snippets": [{"name": snippet.name, "kind": snippet.kind,
                                   "span": [snippet.start, snippet.end], "origin": snippet.origin}
                                  for snippet in snippets]}


def baseline_view(record):
    if record["source"] == MOST_MATCH_SOURCE:
        validate_prompt_context(record)
        return record["metadata"]["prompt_context"]
    hol = record["hol_light_reference_context"]
    isa = record["isabelle_context_before_target"]
    parts, _ = isabelle_snippets(isa)
    return {
        "version": "full_aligned_references_v1", "unit": "characters",
        "policy": "full_aligned_references", "verification_context": "full_original_masked_prefix",
        "hol_light": full_reference_info(hol, source_snippets(hol)),
        "isabelle": full_reference_info(proof_context(record) or isa, parts),
    }


def pair_identity(record):
    # Used to compare the exact same original record across arms.
    return fingerprint([key(record), record["hol_light_statement"], record["hol_light_proof"],
                        record["isabelle_statement"], record["isabelle_proof_prefix"],
                        record["isabelle_theory_template"], record["metadata"]])


def arm_record(record, arm, *, support_sha256=None, prompt_context=None, pair_sha256=None):
    metadata = {**record["metadata"], "context_experiment": {
        "version": VERSION, "arm": arm, "pair_sha256": pair_sha256 or pair_identity(record),
        "support_sha256": support_sha256}}
    if prompt_context is not None:
        metadata["prompt_context"] = prompt_context
    return {**record, "metadata": metadata}


def selection_change(before, after):
    def locations(info):
        return {(item["name"], item.get("origin", ""), tuple(item["span"])) for item in info["selected_snippets"]}

    earlier, later = locations(before), locations(after)
    return {"before_chars": before["selected_chars"], "after_chars": after["selected_chars"],
            "gained": sorted(later - earlier), "dropped": sorted(earlier - later)}


@dataclass
class ContextSelection:
    record: dict
    config: ContextConfig
    baseline: dict
    isabelle_budget: int
    graph: dict
    helpers: list
    hol_reference: str
    hol_info: dict
    ranked: list
    scopes: list
    shortlist: dict
    imports: dict
    proof_sources: dict | None

    def render(self, *, mode="context", inspection=None, backend_sha256=None):
        baseline = self.baseline
        target_reference, target_info, evidence = target_facts.select_target(
            self.ranked, self.scopes, self.shortlist, self.imports,
            budget=self.isabelle_budget, inspection=inspection, proof_sources=self.proof_sources)
        policy = {"version": DEPENDENCY_CONTEXT_VERSION, "unit": "characters",
                  "hol_light": self.hol_info, "isabelle": target_info,
                  "policy": "bounded_dependency_references",
                  "verification_context": "full_original_masked_prefix"}
        context = context_arm(native=inspection is not None, cross_file=self.config.cross_file)
        arm = context_arm(native=inspection is not None, cross_file=self.config.cross_file, mode=mode)
        settings = asdict(self.config)
        ignored = EXPANSION_SETTINGS + (() if self.config.cross_file else LOAD_SETTINGS)
        if self.record["source"] == MOST_MATCH_SOURCE:
            ignored += ALIGNED_CAP_SETTINGS
        settings = {name: value for name, value in settings.items() if name not in ignored}
        report = {"target": list(key(self.record)), "arm": context, "status": "selected",
                  "baseline": baseline, "selection": policy,
                  "changes": {name: selection_change(baseline[name], policy[name])
                              for name in ("hol_light", "isabelle")},
                  "dependency_graph": self.graph, "target_candidates": evidence,
                  "settings": settings, "backend_sha256": backend_sha256}
        if inspection is not None:
            report["fact_inspection_version"] = inspection["version"]
        row = arm_record(self.record, context, support_sha256=fingerprint(report), prompt_context=policy)
        row["hol_light_reference_context"] = self.hol_reference
        row["isabelle_prompt_context"] = target_reference
        if self.proof_sources is not None:
            local = self.proof_sources[""]
            store_context(row, target_reference, selected_reference_proofs(target_info),
                          status=local.status if local is not None else "missing_proof_snapshot")
        row["metadata"]["hol_light_stmt_sha256"] = sha256(self.hol_reference)
        validate_prompt_context(row)
        if mode == "expand":
            base = dataset_for(row).prompt(row)
            base_size = len(base.system_prompt) + len(base.user_prompt)
            bundle, expansion = select_source_helpers(self.helpers, self.graph, evidence, self.config,
                                                       base_prompt_chars=base_size)
            report.update(arm=arm, source_helper_expansion=expansion,
                          settings={**settings, **{name: getattr(self.config, name) for name in EXPANSION_SETTINGS}})
            metadata = row["metadata"]["context_experiment"]
            metadata.update(arm=arm, support_sha256=fingerprint(report))
            metadata[BUNDLE_DIGEST] = expansion["bundle_sha256"]
            row[BUNDLE_FIELD] = bundle
        return row, report


def prepare_selection(record, config, *, dataset_root=DATASET_ROOT, catalog=None):
    baseline = baseline_view(record)
    source = load_source(record, config, dataset_root=dataset_root)
    helpers, hints, graph, definitions = walk(source, config, catalog=catalog)
    pinned, eligible, packages = source_packages(source, helpers, graph)
    source_budget = baseline["hol_light"]["budget_chars"] or config.source_context_chars
    isabelle_budget = baseline["isabelle"]["budget_chars"] or config.isabelle_context_chars
    selection = Selection(source_budget, pinned)
    for node, snippet, required in packages:
        node["selection"] = ("selected" if selection.add_optional(snippet, required) else "over_budget")
        node["reference_span"] = [snippet.start, snippet.end]
        node["reference_chars"] = len(snippet.text)
        node["vocabulary"] = [entry.name for entry in required]
    imported = []
    for snippet, edge in imported_definitions(definitions):
        edge["reference_selection"] = "selected" if selection.add_optional(snippet) else "over_budget"
        edge["reference_path"] = snippet.origin
        edge["reference_span"] = [snippet.start, snippet.end]
        imported.append(snippet)
    query = identifiers(source.root.statement + "\n" + source.root.proof)
    helper_symbols = frozenset().union(*(identifiers(helper.binding.statement) for helper in helpers))
    query |= helper_symbols
    ranked = sorted(eligible, key=lambda item: (-len(identifiers(item.text) & query), -item.start, item.name))
    for item in ranked:
        if identifiers(item.text) & query:
            selection.add_optional(item)
    candidates = [*pinned, *eligible, *imported]
    if config.cross_file:
        for node, snippet, required in packages:
            if snippet.origin:
                node["reference_path"] = snippet.origin
                candidates.extend([snippet, *required])
        candidates = list(dict.fromkeys(candidates))
    hol_reference, hol_info = selection.finish(candidates)
    target = target_facts.candidates(record, hints, helper_symbols, config, dataset_root=dataset_root)
    return ContextSelection(record, config, baseline, isabelle_budget, graph, helpers, hol_reference, hol_info, *target)
