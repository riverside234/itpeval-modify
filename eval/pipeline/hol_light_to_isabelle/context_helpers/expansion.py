"""Select complete source proof packages from the existing bounded dependency graph."""

from collections import Counter, defaultdict, deque

from ..babel_formal_pipeline.common import fingerprint
from ..hundred_theorems_pipeline.hol_syntax import tokens
from .contracts import SelectionFailure
from .prompts import BUNDLE_VERSION, render_support

FOLLOWED_EDGES = {"explicit_reference", "resolved_alias"}


def _order_helpers(admitted, edges):
    """Keep each child before all of its admitted dependents."""
    ordered, active, visited = [], set(), set()

    def visit(identity):
        if identity in active:
            raise SelectionFailure("dependency_cycle", "source helper graph contains a proof dependency cycle")
        if identity in visited:
            return
        active.add(identity)
        for edge in edges[identity]:
            child = edge.get("child")
            if edge["status"] in FOLLOWED_EDGES and child in admitted:
                visit(child)
        active.remove(identity)
        visited.add(identity)
        ordered.append(admitted[identity])

    for identity in admitted:
        visit(identity)
    return ordered


def _candidate_facts(name, evidence):
    return [
        {"name": fact.get("name", fact["requested"]), "availability": fact["availability"],
         "scope": fact["scope"], "selection": fact["selection"]}
        for fact in evidence
        if (fact.get("source_name_match") or "").casefold() == name.casefold()
    ]


def _dependency_reference(edge, *, short_id=False):
    reference = {"name": edge.get("name"), "evidence": edge["status"]}
    if "child" in edge:
        identity = edge["child"][:12] if short_id else edge["child"]
        reference.update(name=edge["child_name"], id=identity)
    if "alias_chain" in edge:
        reference["via"] = edge["alias_chain"]
    if "omitted" in edge:
        reference["omitted"] = edge["omitted"]
    return reference


def _package(location, node, references, facts):
    source, binding = location.source, location.binding
    return {
        "id": node["id"], "name": binding.name, "statement": binding.statement, "proof": binding.proof,
        "references": {
            "source": source.proof_path, "span": node["span"],
            **({"load_chain": node["load_chain"]} if node.get("load_chain") else {}),
            "dependencies": [_dependency_reference(edge, short_id=True) for edge in references],
            "masked_reference": node.get("selection", "unavailable"),
            "definitions": node.get("vocabulary", []),
            "isabelle_candidates": [
                {"name": fact["name"], "availability": fact["availability"]} for fact in facts
                if fact["selection"] == "selected"
            ],
        },
    }


def select_source_helpers(helpers, graph, target_evidence, config, *, base_prompt_chars):
    nodes = {node["id"]: node for node in graph["nodes"][1:]}
    names = Counter(node["name"].casefold() for node in nodes.values())
    locations = {location.identity: location for location in helpers}
    edges, parents = defaultdict(list), defaultdict(list)
    for edge in graph["edges"]:
        edges[edge["parent"]].append(edge)
        if edge.get("child") in nodes:
            parents[edge["child"]].append({"id": edge["parent"], "reference": edge["name"],
                                           "evidence": edge["status"]})

    def followed(parent):
        return (edge["child"] for edge in edges[parent]
                if edge["status"] in FOLLOWED_EDGES and edge.get("child") in nodes)

    admitted, decisions = {}, {}
    proof_chars, support_chars = 0, 0
    pending = deque(followed(graph["root"]))
    while pending:
        identity = pending.popleft()
        if identity in decisions:
            continue
        node, location = nodes[identity], locations.get(identity)
        candidates = _candidate_facts(node["name"], target_evidence)
        decision = {"status": "source_unavailable", "isabelle_candidates": candidates}
        if location is not None:
            decision["proof_chars"] = len(location.binding.proof)
        decisions[identity] = decision
        # Live name resolution is a ranking signal. The instance and alignment
        # still need checking in the actual proof state.
        available = {fact["name"] for fact in candidates if fact["availability"] == "resolved"}
        visible = {fact["name"] for fact in candidates
                   if fact["availability"] == "resolved" and fact["selection"] == "selected"}
        if names[node["name"].casefold()] == 1 and len(available) == 1 and visible:
            decision["status"] = "native_candidate_supplied"
            continue
        if (location is None or location.binding.kind != "theorem" or not location.binding.statement
                or not location.binding.proof or node["name"] == graph["nodes"][0]["name"]):
            continue
        proof = location.binding.proof
        if len(proof) > config.max_helper_proof_chars:
            decision.update(status="proof_too_large", limit="max_helper_proof_chars")
            continue
        if len(proof) + proof_chars > config.max_total_helper_proof_chars:
            decision.update(status="budget_exhausted", limit="max_total_helper_proof_chars")
            continue
        words = [token.text for token in tokens(proof) if token.kind == "word"]
        if not words or {"SORRY", "ADMIT", "CHEAT_TAC"}.intersection(word.upper() for word in words):
            decision["status"] = "incomplete_source_proof"
            continue
        package = _package(location, node, edges[identity], candidates)
        size = len(render_support([*admitted.values(), package]))
        decision["added_support_chars"] = size - support_chars
        if size > config.max_helper_support_chars:
            decision.update(status="budget_exhausted", limit="max_helper_support_chars")
            continue
        if base_prompt_chars + size > config.max_prompt_chars:
            decision.update(status="budget_exhausted", limit="max_prompt_chars")
            continue
        admitted[identity] = package
        proof_chars += len(proof)
        support_chars = size
        decision["status"] = "included"
        pending.extend(followed(identity))

    bundle = {"version": BUNDLE_VERSION, "helpers": _order_helpers(admitted, edges)}
    reports = []
    for identity, node in nodes.items():
        location = locations.get(identity)
        decision = decisions.get(identity, {"status": "parent_not_expanded"})
        dependencies = []
        for edge in edges[identity]:
            reference = _dependency_reference(edge)
            if edge["status"] in FOLLOWED_EDGES:
                child = decisions.get(edge.get("child"), {})
                reference["support"] = child.get("status", "source_unavailable")
            elif edge["status"] == "definition_reference":
                reference["support"] = edge.get("reference_selection", "earlier_source_definition")
            dependencies.append(reference)
        reports.append({
            **node, **decision, "alignment_status": "unreviewed", "parents": parents[identity],
            "source_path": location.source.proof_path if location else node.get("source_path"),
            "source_sha256": location.source.proof_sha256 if location else node.get("source_sha256"),
            "dependencies": dependencies,
        })
    report = {
        "bundle_sha256": fingerprint(bundle), "base_prompt_chars": base_prompt_chars,
        "proof_chars": proof_chars, "support_chars": support_chars,
        "included": [item["id"] for item in bundle["helpers"]],
        "counts": dict(Counter(node["status"] for node in reports)), "nodes": reports,
    }
    return bundle, report
