"""Bounded static traversal of HOL Light proof references."""

from __future__ import annotations

from collections import deque

from ..hundred_theorems_pipeline.hol_syntax import tokens
from ..most_match_pipeline.context import identifiers
from .contracts import SelectionFailure


def _proof_words(proof):
    items = tokens(proof)
    # Conservative for simple let/function patterns. Suppress a possible local
    # binding throughout this proof fragment rather than attributing it globally.
    local = set()
    for i, item in enumerate(items):
        if item.text not in {"let", "fun"}:
            continue
        for j in range(i + 1, len(items)):
            part = items[j]
            if part.text == "=" or (part.text == "-" and j + 1 < len(items) and items[j + 1].text == ">"):
                break
            if part.kind == "word":
                local.add(part.text)
    return list(dict.fromkeys(item.text for item in items if item.kind == "word")), local


def walk(source, config):
    index, root = source.index, source.root
    pending = deque([(root, 0)])
    reached = {root.start: 0}
    helpers, edges, hints = [], [], []
    while pending:
        parent, depth = pending.popleft()
        words, local = _proof_words(parent.proof)
        known = [name for name in words if name in index.bindings]
        unknown = [name for name in words if name not in index.bindings and name not in local
                   and name.isupper() and "_" in name and not name.endswith("_TAC")]
        names = known + unknown
        if len(names) > config.max_edges_per_node:
            edges.append({"parent": source.identity(parent), "status": "edge_scan_limit",
                          "omitted": len(names) - config.max_edges_per_node})
        for name in names[:config.max_edges_per_node]:
            edge = {"parent": source.identity(parent), "name": name, "depth": depth + 1}
            edges.append(edge)
            if name in local:
                edge["status"] = "possible_local_binding"
                continue
            child, status, aliases = index.resolve(name, before=parent.start, root=root)
            edge["status"] = status
            if aliases:
                edge["alias_chain"] = aliases
            if status in {"explicit_reference", "resolved_alias", "definition_reference", "unresolved_reference"}:
                hints.append(name)
            if child is None:
                if name not in index.bindings and not aliases and status == "unresolved_reference":
                    edge["status"] = "unresolved_identifier"
                continue
            hints.append(child.name)
            edge.update(child=source.identity(child), child_name=child.name, child_span=[child.start, child.end])
            if child.kind != "theorem":
                continue
            if child.start in reached:
                edge["shared_child"] = True
                continue
            if depth >= config.dependency_depth:
                edge.update(status="depth_limit", evidence=status)
                continue
            if len(helpers) >= config.max_helpers:
                edge.update(status="node_limit", evidence=status)
                continue
            reached[child.start] = depth + 1
            helpers.append(child)
            pending.append((child, depth + 1))
    nodes = [{**index.describe(binding), "id": source.identity(binding), "depth": reached[binding.start]}
             for binding in [root, *helpers]]
    return helpers, list(dict.fromkeys(hints)), {
        "source_path": source.proof_path, "source_sha256": source.proof_sha256,
        "masked_path": source.statement_path, "masked_sha256": source.statement_sha256,
        "root": source.identity(root), "nodes": nodes, "edges": edges,
        "loads": [item for item in index.loads if item["offset"] < root.start],
        "opaque_prior_phrases": sum(offset < root.start for offset in index.opaque_phrases),
        "coverage": "static_same_file_references",
    }


def source_packages(source, helpers, graph):
    """Pair each followed theorem with its unique earlier proof-masked statement."""
    root = source.root
    pinned = [snippet for snippet in source.snippets if snippet.name == root.name]
    if len(pinned) != 1:
        raise SelectionFailure("source_snapshot_mismatch", "masked root statement is missing or ambiguous")
    eligible = [snippet for snippet in source.snippets if snippet.start < pinned[0].start]
    definitions = [snippet for snippet in eligible if snippet.kind == "definition"]
    packages = []
    by_name = {}
    for snippet in eligible:
        if snippet.kind == "statement":
            by_name.setdefault(snippet.name, []).append(snippet)
    for binding, node in zip(helpers, graph["nodes"][1:]):
        statement = " ".join(binding.statement.split())
        matches = [snippet for snippet in by_name.get(binding.name, ())
                   if " ".join(tokens(snippet.text)[3].text[1:-1].split()) == statement]
        if len(matches) != 1:
            node["selection"] = "ambiguous_masked_statement" if matches else "masked_statement_unavailable"
            continue
        snippet = matches[0]
        vocabulary = identifiers(binding.statement)
        required = [candidate for candidate in definitions
                    if candidate.start < snippet.start and candidate.name.casefold() in vocabulary]
        packages.append((node, snippet, required))
    return pinned, eligible, packages
