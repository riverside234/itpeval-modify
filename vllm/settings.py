"""Server-side path, checkpoint, and cache utilities (standard library only)."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]


def repo_path(value: str | Path) -> Path:
    value = Path(value).expanduser()
    value = (value if value.is_absolute() else ROOT/value).resolve()
    if not value.is_relative_to(ROOT.resolve()):
        raise ValueError("server path must remain under ITPEval: "+str(value))
    return value


def cache_environment(*, create: bool = True) -> dict[str,str]:
    paths = {
        "CONDA_PKGS_DIRS":"conda", "PIP_CACHE_DIR":"pip",
        "HF_HOME":"huggingface","HF_HUB_CACHE":"huggingface/hub",
        "XDG_CACHE_HOME":"xdg","TORCH_HOME":"torch",
        "TORCHINDUCTOR_CACHE_DIR":"torchinductor","TRITON_CACHE_DIR":"triton",
        "VLLM_CACHE_ROOT":"vllm","CUDA_CACHE_PATH":"cuda",
        "TMPDIR":"tmp","TMP":"tmp","TEMP":"tmp",
    }
    result = {name:str(repo_path("vllm/cache/"+path)) for name,path in paths.items()}
    if create:
        for path in set(result.values()):
            Path(path).mkdir(parents=True,exist_ok=True)
    return result


def read_config(path: str | Path = "vllm/server.example.json") -> dict:
    data = json.loads(repo_path(path).read_text(encoding="utf-8"))
    expected = {"model","revision","model_dir","host","port","cuda_visible_devices","dtype",
                "quantization","tensor_parallel_size","max_model_len","max_num_seqs",
                "gpu_memory_utilization","manifest","log","expected_versions"}
    if not isinstance(data,dict) or set(data) != expected:
        raise ValueError("server config must contain exactly the documented server.example.json fields")
    if not isinstance(data["model"],str) or not data["model"].strip():
        raise ValueError("missing checkpoint model ID")
    if not re.fullmatch(r"[0-9a-f]{40}",data["revision"]):
        raise ValueError("revision must be a full checkpoint commit")
    if not isinstance(data["host"],str) or not data["host"]:
        raise ValueError("missing host")
    for name in ("port","tensor_parallel_size","max_model_len","max_num_seqs"):
        if isinstance(data[name],bool) or not isinstance(data[name],int) or data[name]<1:
            raise ValueError(name+" must be a positive integer")
    if data["port"]>65535 or data["max_model_len"]>262144:
        raise ValueError("invalid port or context exceeds the native Qwen context")
    if data["dtype"] not in {"bfloat16","float16","auto"}:
        raise ValueError("unsupported dtype")
    if data["quantization"] is not None and not isinstance(data["quantization"],str):
        raise ValueError("quantization must be null or an explicit method")
    if (isinstance(data["gpu_memory_utilization"],bool)
            or not isinstance(data["gpu_memory_utilization"],(int,float))
            or not 0<data["gpu_memory_utilization"]<1):
        raise ValueError("gpu_memory_utilization must be in (0, 1)")
    if not isinstance(data["cuda_visible_devices"],str):
        raise ValueError("cuda_visible_devices must be a string")
    versions = data["expected_versions"]
    if not isinstance(versions,dict) or set(versions)!={"vllm","transformers","huggingface-hub"} or any(not isinstance(v,str) for v in versions.values()):
        raise ValueError("expected_versions must pin vllm, transformers, and huggingface-hub")
    for name in ("model_dir","manifest","log"):
        repo_path(data[name])
    if repo_path(data["manifest"]) == repo_path(data["log"]):
        raise ValueError("server manifest and log must be separate files")
    return data


def file_hash(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda:stream.read(1024*1024),b""):
            value.update(block)
    return value.hexdigest()


def metadata_hashes(directory: Path) -> dict:
    tokenizer = {}
    templates = {}
    for path in directory.iterdir():
        if path.is_file() and (path.name.startswith(("tokenizer","special_tokens","vocab","merges"))
                               or "chat_template" in path.name):
            tokenizer[path.name] = file_hash(path)
        if path.is_file() and ("chat_template" in path.name or path.name=="tokenizer_config.json"):
            templates[path.name] = file_hash(path)
    if not tokenizer or not templates:
        raise ValueError("checkpoint has no tokenizer or chat template metadata")
    def hash_map(value):
        return hashlib.sha256(json.dumps(value,sort_keys=True).encode()).hexdigest()
    return {"tokenizer_sha256":hash_map(tokenizer),"template_sha256":hash_map(templates)}


def verify_checkpoint(config: dict) -> dict:
    directory = repo_path(config["model_dir"])
    path = directory/".itpeval_download.json"
    if not path.is_file():
        raise ValueError("missing pinned download manifest; run vllm/download_model.py")
    manifest = json.loads(path.read_text(encoding="utf-8"))
    if (manifest.get("model")!=config["model"] or manifest.get("revision")!=config["revision"]
            or manifest.get("schema_version")!="itpeval_checkpoint_v1"):
        raise ValueError("download manifest does not match server checkpoint")
    files = manifest.get("files",{})
    if not isinstance(files,dict) or not files or not any(name.endswith(".safetensors") for name in files):
        raise ValueError("checkpoint manifest contains no model weights")
    for name,size in files.items():
        path = (directory/name).resolve()
        if not path.is_relative_to(directory) or not path.is_file() or path.stat().st_size!=size:
            raise ValueError("missing or incomplete checkpoint file: "+name)
    hashes = metadata_hashes(directory)
    if any(manifest.get(name)!=value for name,value in hashes.items()):
        raise ValueError("checkpoint tokenizer/template was modified")
    return manifest
