"""Contract and direct Sketch prompt for complete HOL Light helper proofs."""

import json
import re

from ..babel_formal_pipeline.common import fingerprint

BUNDLE_FIELD = "source_helper_bundle"
BUNDLE_DIGEST = "source_helper_bundle_sha256"
BUNDLE_VERSION = "hol_light_source_helper_bundle_v1"
EXPAND_PROMPT_VERSION = "expand_p1"

EXPANSION_RULES = (
    "COMPLETED HOL LIGHT HELPER PROOFS\n"
    "These packages provide source evidence for the selected proof. Some dependencies "
    "appear only as references because their proofs were unavailable or outside the "
    "selection budget. Isabelle candidate names refer to the supplied reference "
    "signatures. Check the actual types, premises, and conclusion before applying one.\n"
    "For each needed instance that still requires a proof, use the relevant source "
    "steps to establish a local have in the main Isabelle proof. Prove children "
    "before their dependents in the scope where their variables and premises are "
    "available. Discharge each required premise from the oracle assumptions, "
    "background, or proved local facts. Close each local proof with an Isabelle "
    "method. For an unresolved step, use a standalone sledgehammer gap with the "
    "relevant local facts. Use existing target definitions. "
    "Keep the oracle declaration and proof prefix fixed, and return one main proof body."
)


def is_expansion(record):
    arm = record.get("metadata", {}).get("context_experiment", {}).get("arm", "")
    return arm.split("-", 1)[0] == "expand"


def direct_prompt_version(record, base_version):
    if is_expansion(record):
        return f"{base_version}_{EXPAND_PROMPT_VERSION}"
    return base_version


def validate_bundle(record):
    """Check the published bundle against the digest of the consumed source evidence."""
    if not is_expansion(record):
        if BUNDLE_FIELD in record:
            raise ValueError("source helper bundle requires an expand experiment arm")
        return None
    bundle = record.get(BUNDLE_FIELD)
    digest = record["metadata"]["context_experiment"].get(BUNDLE_DIGEST)
    if (not isinstance(bundle, dict) or bundle.get("version") != BUNDLE_VERSION
            or not isinstance(bundle.get("helpers"), list) or fingerprint(bundle) != digest):
        raise ValueError("missing, unsupported or stale source helper bundle")
    seen = set()
    for helper in bundle["helpers"]:
        if (not isinstance(helper, dict)
                or any(not isinstance(helper.get(field), str) or not helper[field].strip()
                       for field in ("id", "name", "statement", "proof"))
                or not isinstance(helper.get("references"), dict)
                or helper["id"] in seen or helper["name"] == record.get("hol_light_target_name")):
            raise ValueError("invalid source helper package")
        seen.add(helper["id"])
    return bundle


def _quoted(text):
    # Use a fence longer than any run of tildes in the source.
    longest = max((len(match.group()) for match in re.finditer(r"~{3,}", text)), default=2)
    fence = "~" * (longest + 1)
    return f"{fence}\n{text}\n{fence}"


def render_helper(helper):
    return (
        f"HOL Light helper {helper['name']} [{helper['id'][:12]}]\n"
        + json.dumps(helper["references"], ensure_ascii=False, separators=(", ", ": "))
        + "\nStatement\n" + _quoted(helper["statement"])
        + "\nCompleted proof\n" + _quoted(helper["proof"])
    )


def render_support(helpers):
    if not helpers:
        return ""
    return "\n\n" + EXPANSION_RULES + "\n\n" + "\n\n".join(map(render_helper, helpers))
