"""Build a prompt view and a reproducible selection report for most-match."""

from dataclasses import asdict, dataclass

from ..most_match_pipeline.common import DATASET_ROOT, fingerprint, key, sha256
from ..most_match_pipeline.context import (DEPENDENCY_CONTEXT_VERSION, identifiers,
                                          validate_prompt_context)
from .contracts import ContextConfig, LOAD_SETTINGS, VERSION, context_arm
from .dependencies import imported_definitions, source_packages, walk
from .selection import Selection
from .source_index import load_source
from . import target_facts


def baseline_view(record):
    return record["metadata"]["prompt_context"]


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
    graph: dict
    hol_reference: str
    hol_info: dict
    ranked: list
    scopes: list
    shortlist: dict
    imports: dict

    def render(self, *, inspection=None, backend_sha256=None):
        baseline = baseline_view(self.record)
        target_reference, target_info, evidence = target_facts.select_target(
            self.ranked, self.scopes, self.shortlist, self.imports,
            budget=baseline["isabelle"]["budget_chars"], inspection=inspection)
        policy = {"version": DEPENDENCY_CONTEXT_VERSION, "unit": "characters",
                  "hol_light": self.hol_info, "isabelle": target_info,
                  "policy": "bounded_dependency_references",
                  "verification_context": "full_original_masked_prefix"}
        arm = context_arm(native=inspection is not None, cross_file=self.config.cross_file)
        settings = asdict(self.config)
        if not self.config.cross_file:
            settings = {name: value for name, value in settings.items() if name not in LOAD_SETTINGS}
        report = {"target": list(key(self.record)), "arm": arm, "status": "selected",
                  "baseline": baseline, "selection": policy,
                  "changes": {name: selection_change(baseline[name], policy[name])
                              for name in ("hol_light", "isabelle")},
                  "dependency_graph": self.graph, "target_candidates": evidence,
                  "settings": settings, "backend_sha256": backend_sha256}
        if inspection is not None:
            report["fact_inspection_version"] = inspection["version"]
        row = arm_record(self.record, arm, support_sha256=fingerprint(report), prompt_context=policy)
        row["hol_light_reference_context"] = self.hol_reference
        row["isabelle_prompt_context"] = target_reference
        row["metadata"]["hol_light_stmt_sha256"] = sha256(self.hol_reference)
        validate_prompt_context(row)
        return row, report


def prepare_selection(record, config, *, dataset_root=DATASET_ROOT, catalog=None):
    validate_prompt_context(record)
    source = load_source(record, config, dataset_root=dataset_root)
    helpers, hints, graph, definitions = walk(source, config, catalog=catalog)
    pinned, eligible, packages = source_packages(source, helpers, graph)
    baseline = baseline_view(record)
    selection = Selection(baseline["hol_light"]["budget_chars"], pinned)
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
    return ContextSelection(record, config, graph, hol_reference, hol_info, *target)
