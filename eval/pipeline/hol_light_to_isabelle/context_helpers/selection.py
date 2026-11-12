"""Fit whole reference packages without spending mandatory scope space."""

from ..most_match_pipeline.common import sha256
from ..most_match_pipeline.context import render_snippet
from .contracts import SelectionFailure


class Selection:
    def __init__(self, budget, required):
        self.budget = budget
        self.chars = 0
        self.items = {}
        self.omitted = {}
        if not self.add(required):
            raise SelectionFailure("mandatory_context_overflow", "active scope or masked target exceeds its reference cap")

    @staticmethod
    def span_key(snippet):
        return (snippet.origin, snippet.start, snippet.end)

    def add(self, snippets):
        new = {self.span_key(snippet): snippet for snippet in snippets
               if self.span_key(snippet) not in self.items}
        cost = sum(len(render_snippet(item)) + 2 for item in new.values())
        if new and not self.items:
            cost -= 2
        if self.chars + cost > self.budget:
            return False
        self.items.update(new)
        self.chars += cost
        return True

    def add_optional(self, snippet, required=()):
        anchor = self.span_key(snippet)
        if anchor in self.omitted:
            return False
        if not self.add([*required, snippet]):
            self.omitted[anchor] = "over_budget"
            return False
        return True

    def finish(self, candidates):
        selected = [self.items[key] for key in sorted(self.items)]
        context = "\n\n".join(map(render_snippet, selected))
        if not context:
            context = "(* No relevant reference declarations fit the context selection. *)"
        info = {"budget_chars": self.budget, "selected_chars": len(context), "sha256": sha256(context),
                "candidate_snippets": len(candidates),
                "selected_snippets": [
                    {"name": item.name, "kind": item.kind, "span": [item.start, item.end],
                     "origin": item.origin, "sha256": sha256(item.text)} for item in selected],
                "omitted_snippets": sum(self.span_key(item) not in self.items for item in candidates),
                "over_budget_snippets": len(self.omitted)}
        return context, info
