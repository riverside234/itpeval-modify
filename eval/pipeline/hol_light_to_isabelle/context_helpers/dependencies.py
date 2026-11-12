"""Bounded static traversal of HOL Light proof references."""

from __future__ import annotations

from collections import deque
from dataclasses import replace

from ..hundred_theorems_pipeline.hol_syntax import tokens
from ..most_match_pipeline.context import Snippet, identifiers
from .contracts import SelectionFailure
from .source_loads import LoadCatalog, LoadTimeline, Location


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


def _resolve(name, parent, root, *, preceding, known):
    aliases, seen = [], set()
    location = parent
    for _ in range(9):
        if name == root.binding.name:
            return None, "excluded_target", aliases
        candidate = preceding(name, location)
        if candidate is None:
            if name in seen:
                return None, "cycle_or_forward_alias", aliases
            return None, "not_yet_bound" if name in known else "unresolved_reference", aliases
        binding = candidate.binding
        if binding.kind != "alias":
            status = {"theorem": "resolved_alias" if aliases else "explicit_reference",
                      "definition": "definition_reference", "opaque": "unsupported_binding"}[binding.kind]
            return candidate, status, aliases
        if len(aliases) == 8:
            break
        aliases.append(binding.name)
        seen.add(name)
        name, location = binding.alias, candidate
    return None, "alias_limit", aliases


def walk(source, config, *, catalog=None):
    timeline = LoadTimeline(source, catalog or LoadCatalog(config)) if config.cross_file else None
    root = timeline.root if timeline else Location(source, source.root)
    known = timeline.known if timeline else source.index.bindings

    def preceding(name, location):
        if timeline:
            return timeline.preceding(name, location)
        binding = source.index.preceding(name, location.binding.start)
        return Location(source, binding) if binding is not None else None

    pending = deque([(root, 0)])
    reached = {root.identity: 0}
    helpers, edges, hints = [], [], []
    definitions = {}
    while pending:
        parent, depth = pending.popleft()
        words, local = _proof_words(parent.binding.proof)
        names = [name for name in words if name in known]
        names.extend(name for name in words if name not in known and name not in local
                     and name.isupper() and "_" in name and not name.endswith("_TAC"))
        if len(names) > config.max_edges_per_node:
            edges.append({"parent": parent.identity, "status": "edge_scan_limit",
                          "omitted": len(names) - config.max_edges_per_node})
        for name in names[:config.max_edges_per_node]:
            edge = {"parent": parent.identity, "name": name, "depth": depth + 1}
            edges.append(edge)
            if name in local:
                edge["status"] = "possible_local_binding"
                continue
            child, status, aliases = _resolve(name, parent, root, preceding=preceding, known=known)
            edge["status"] = status
            if aliases:
                edge["alias_chain"] = aliases
            if status in {"explicit_reference", "resolved_alias", "definition_reference", "unresolved_reference"}:
                hints.append(name)
            if child is None:
                if name not in known and not aliases and status == "unresolved_reference":
                    edge["status"] = "unresolved_identifier"
                continue
            binding = child.binding
            hints.append(binding.name)
            edge.update(child=child.identity, child_name=binding.name, child_span=[binding.start, binding.end])
            if timeline:
                edge.update(child_source_path=child.source.proof_path,
                            cross_file=child.source.proof_path != parent.source.proof_path)
            if binding.kind != "theorem":
                if binding.kind == "definition" and child.source.proof_path != source.proof_path:
                    definitions.setdefault(child.identity, (child, edge))
                continue
            if child.identity in reached:
                edge["shared_child"] = True
                continue
            if depth >= config.dependency_depth:
                edge.update(status="depth_limit", evidence=status)
                continue
            if len(helpers) >= config.max_helpers:
                edge.update(status="node_limit", evidence=status)
                continue
            reached[child.identity] = depth + 1
            helpers.append(child)
            pending.append((child, depth + 1))
    nodes = []
    for location in [root, *helpers]:
        node = {**location.source.index.describe(location.binding), "id": location.identity,
                "depth": reached[location.identity]}
        if timeline:
            node.update(timeline.provenance(location))
        nodes.append(node)
    graph = {
        "source_path": source.proof_path, "source_sha256": source.proof_sha256,
        "masked_path": source.statement_path, "masked_sha256": source.statement_sha256,
        "root": root.identity, "nodes": nodes, "edges": edges,
        "loads": [item for item in source.index.loads if item["offset"] < root.binding.start],
        "opaque_prior_phrases": sum(offset < root.binding.start for offset in source.index.opaque_phrases),
        "coverage": "static_same_file_references",
    }
    if timeline:
        graph.update(loads=timeline.loads, coverage="static_ordered_load_references",
                     load_manifest_sha256=timeline.catalog.sha256,
                     loaded_files=len(timeline.units) - 1)
    return helpers, list(dict.fromkeys(hints)), graph, list(definitions.values())


def imported_definitions(references):
    for location, edge in references:
        binding, unit = location.binding, location.source
        original = unit.index.text[binding.start:binding.end]
        signature = [token.text for token in tokens(original)]
        matches = [snippet for snippet in unit.snippets
                   if snippet.kind == "definition" and snippet.name == binding.name
                   and [token.text for token in tokens(snippet.text)] == signature]
        if len(matches) == 1:
            yield replace(matches[0], origin=unit.statement_path), edge
        else:
            edge["reference_selection"] = "ambiguous_masked_definition" if matches else "masked_definition_unavailable"


def source_packages(source, helpers, graph):
    """Pair each followed theorem with a masked statement and local vocabulary."""
    pinned = [snippet for snippet in source.snippets if snippet.name == source.root.name]
    if len(pinned) != 1:
        raise SelectionFailure("source_snapshot_mismatch", "masked root statement is missing or ambiguous")
    eligible = [snippet for snippet in source.snippets if snippet.start < pinned[0].start]
    packages = []
    for location, node in zip(helpers, graph["nodes"][1:]):
        binding, unit = location.binding, location.source
        imported = unit.proof_path != source.proof_path
        candidates = unit.snippets if imported else eligible
        if imported and not unit.statement_path:
            quote = chr(96)
            text = f"let {binding.name} = {quote}{binding.statement}{quote};;"
            snippet = Snippet(binding.name, "statement", binding.start, binding.end, text, unit.proof_path)
            node["reference_kind"] = "statement_from_literal_proof"
            packages.append((node, snippet, []))
            continue
        statement = " ".join(binding.statement.split())
        matches = [snippet for snippet in candidates if snippet.kind == "statement" and snippet.name == binding.name
                   and " ".join(tokens(snippet.text)[3].text[1:-1].split()) == statement]
        if len(matches) != 1:
            node["selection"] = "ambiguous_masked_statement" if matches else "masked_statement_unavailable"
            continue
        snippet = matches[0]
        vocabulary = identifiers(binding.statement)
        required = [candidate for candidate in candidates if candidate.kind == "definition"
                    and candidate.start < snippet.start and candidate.name.casefold() in vocabulary]
        if imported:
            snippet = replace(snippet, origin=unit.statement_path)
            required = [replace(candidate, origin=unit.statement_path) for candidate in required]
            node["reference_kind"] = "masked_snapshot"
        packages.append((node, snippet, required))
    return pinned, eligible, packages
