from __future__ import annotations

import sys
from typing import TypedDict

from eval.pipeline.config import MODELS


class ModelConfig(TypedDict):
    id: str
    provider: str
    label: str


def select_models(labels_csv: str | None, models: list[ModelConfig] | None = None) -> list[ModelConfig]:
    available = models if models is not None else MODELS
    if not labels_csv:
        return available

    # Fail early on misspelled model labels so long eval runs do not start partially
    wanted = {label.strip() for label in labels_csv.split(",") if label.strip()}
    known = {m["label"] for m in available}
    unknown = wanted - known
    if unknown:
        sys.exit(
            "Unknown model label(s): "
            f"{', '.join(sorted(unknown))}. Known labels: {', '.join(sorted(known))}"
        )
    return [m for m in available if m["label"] in wanted]
