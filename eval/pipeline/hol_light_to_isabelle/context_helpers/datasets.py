"""The dataset-specific inputs and direct Sketch prompts for the helper experiments."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

from ..babel_formal_pipeline import aligned_data as babel_data
from ..babel_formal_pipeline.common import RESULTS_DIR as BABEL_RESULTS
from ..babel_formal_pipeline.prompt import Prompt
from ..babel_formal_pipeline.v2_dsp import direct_sketch_prompt as babel_prompt
from ..hundred_theorems_pipeline import aligned_data as hundred_data
from ..hundred_theorems_pipeline.common import RESULTS_DIR as HUNDRED_RESULTS, SOURCE as HUNDRED_SOURCE
from ..hundred_theorems_pipeline.v2_dsp import direct_sketch_prompt as hundred_prompt
from ..most_match_pipeline.common import RESULTS_DIR as MOST_MATCH_RESULTS, SOURCE as MOST_MATCH_SOURCE
from ..most_match_pipeline.v2_dsp import direct_sketch_prompt as most_match_prompt
from .contracts import SelectionFailure


@dataclass(frozen=True)
class Dataset:
    source: str
    results_dir: str
    prompt: Callable[[dict], Prompt]
    prompt_version: str
    load_topic: Callable[[int], babel_data.AlignedTopic] | None = None


DATASETS = {
    "babel-formal": Dataset("babel-formal", BABEL_RESULTS, babel_prompt.build_direct_sketch_prompt,
                            babel_prompt.DIRECT_PROMPT_VERSION, babel_data.load_topic),
    "hundred-theorems": Dataset(HUNDRED_SOURCE, HUNDRED_RESULTS, hundred_prompt.build_direct_sketch_prompt,
                                hundred_prompt.DIRECT_PROMPT_VERSION, hundred_data.load_topic),
    "most-match": Dataset(MOST_MATCH_SOURCE, MOST_MATCH_RESULTS, most_match_prompt.build_direct_sketch_prompt,
                          most_match_prompt.DIRECT_PROMPT_VERSION),
}
BY_SOURCE = {dataset.source: dataset for dataset in DATASETS.values()}


def dataset_for(record):
    source = record.get("source")
    if source not in BY_SOURCE:
        raise ValueError(f"unsupported context experiment dataset: {source!r}")
    return BY_SOURCE[source]


def aligned_topic(record):
    dataset = dataset_for(record)
    try:
        topic = dataset.load_topic(int(record["theorem_id"]))
    except KeyError as exc:
        raise SelectionFailure("source_snapshot_mismatch", "missing aligned dataset row; re-extract records") from exc
    if topic.topic != record["topic"] or topic.tier != record["tier"]:
        raise SelectionFailure("source_snapshot_mismatch", "aligned dataset identity changed; re-extract records")
    return topic
