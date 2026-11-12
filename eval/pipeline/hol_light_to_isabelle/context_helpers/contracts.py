"""Budgets and identities for the context-only experiment."""

from dataclasses import dataclass
import json

from ..most_match_pipeline.common import repo_path
from ..babel_formal_pipeline.v2_dsp.native_search import MAX_INSPECT_FACTS

VERSION = "hol_light_to_isabelle_context_v1"
MODE = "hol-light-proof"
DEFAULT_LOAD_MANIFEST = "eval/configs/hol_light_to_isabelle/context_hol_light_loads.json"
LOAD_SETTINGS = ("cross_file", "source_load_manifest", "max_load_depth", "max_load_files", "max_load_directives")
NATIVE_ARMS = {"context-native", "context-native-cross-file"}


def context_arm(*, native, cross_file):
    arm = "context-native" if native else "context"
    return arm + "-cross-file" if cross_file else arm


@dataclass(frozen=True)
class ContextConfig:
    dependency_depth: int = 2
    max_helpers: int = 5
    max_edges_per_node: int = 64
    max_source_chars: int = 3_000_000
    max_source_phrases: int = 12_000
    max_import_files: int = 16
    max_import_chars: int = 256_000
    max_fact_candidates: int = 24
    max_prompt_chars: int = 100_000
    cross_file: bool = False
    source_load_manifest: str = DEFAULT_LOAD_MANIFEST
    max_load_depth: int = 8
    max_load_files: int = 16
    max_load_directives: int = 128

    def __post_init__(self):
        if type(self.cross_file) is not bool:
            raise ValueError("cross_file must be a boolean")
        if not isinstance(self.source_load_manifest, str) or not self.source_load_manifest.strip():
            raise ValueError("source_load_manifest must be a repository-local path")
        limits = {
            "dependency_depth": (1, 8),
            "max_helpers": (1, 64),
            "max_edges_per_node": (1, 256),
            "max_source_chars": (256, 8_000_000),
            "max_source_phrases": (1, 40_000),
            "max_import_files": (0, 64),
            "max_import_chars": (256, 1_000_000),
            "max_fact_candidates": (1, MAX_INSPECT_FACTS),
            "max_prompt_chars": (256, 1_000_000),
            "max_load_depth": (1, 32),
            "max_load_files": (1, 64),
            "max_load_directives": (1, 512),
        }
        for name, (minimum, maximum) in limits.items():
            value = getattr(self, name)
            if type(value) is not int or not minimum <= value <= maximum:
                raise ValueError(f"{name} must be an integer in {minimum}..{maximum}")

    @classmethod
    def load(cls, path):
        if path is None:
            return cls()
        data = json.loads(repo_path(path).read_text(encoding="utf-8"))
        if not isinstance(data, dict) or set(data) - set(cls.__dataclass_fields__):
            raise ValueError("expected a context helper configuration with known fields")
        return cls(**data)


class SelectionFailure(ValueError):
    def __init__(self, category, message):
        super().__init__(message)
        self.category = category
