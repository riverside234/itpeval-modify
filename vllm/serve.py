"""Validate the isolated environment and exec the official vLLM server."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import importlib.metadata as packages
import hashlib
import json
import os
from pathlib import Path
import platform
import socket
import sys

from settings import ROOT, cache_environment, read_config, repo_path, verify_checkpoint


def command(config: dict) -> list[str]:
    result = [
        sys.executable,"-m","vllm.entrypoints.cli.main","serve",
        str(repo_path(config["model_dir"])),
        "--served-model-name",config["model"],
        "--host",config["host"],"--port",str(config["port"]),
        "--dtype",config["dtype"],"--tensor-parallel-size",str(config["tensor_parallel_size"]),
        "--max-model-len",str(config["max_model_len"]),"--max-num-seqs",str(config["max_num_seqs"]),
        "--gpu-memory-utilization",str(config["gpu_memory_utilization"]),
        "--reasoning-parser","qwen3","--language-model-only","--generation-config","vllm",
    ]
    if config["quantization"]:
        result.extend(["--quantization",config["quantization"]])
    return result


def preflight(config: dict) -> dict:
    if platform.system()!="Linux":
        raise ValueError("the native vLLM server requires the Linux lab environment")
    conda_prefix = os.environ.get("CONDA_PREFIX")
    if not conda_prefix:
        raise ValueError("activate the Python 3.12 server environment: conda activate vllm")
    if Path(sys.prefix).resolve()!=Path(conda_prefix).expanduser().resolve():
        raise ValueError("Python must come from the active conda environment; run conda activate vllm")
    if sys.version_info[:2]!=(3,12):
        raise ValueError("the vLLM server requires Python 3.12; run conda activate vllm")
    versions = {name:packages.version(name) for name in config["expected_versions"]}
    for name,expected in config["expected_versions"].items():
        if versions[name]!=expected:
            raise ValueError(f"{name} must be {expected}, found {versions[name]}")
    checkpoint = verify_checkpoint(config)
    import torch
    if not torch.cuda.is_available():
        raise ValueError("CUDA GPU is unavailable in the server environment")
    if torch.cuda.device_count()<config["tensor_parallel_size"]:
        raise ValueError("not enough visible GPUs for tensor_parallel_size")
    gpu = []
    for index in range(torch.cuda.device_count()):
        prop = torch.cuda.get_device_properties(index)
        if config["dtype"]=="bfloat16" and prop.major<8:
            raise ValueError("bfloat16 requires supported GPU hardware; choose float16 explicitly if needed")
        gpu.append({"index":index,"name":prop.name,"memory_bytes":prop.total_memory,
                    "capability":[prop.major,prop.minor]})
    versions.update(torch=torch.__version__,cuda=torch.version.cuda,python=platform.python_version(),
                    environment_sha256=hashlib.sha256(package_freeze().encode()).hexdigest())
    return {
        "schema_version":"itpeval_qwen_server_v1","model":config["model"],
        "model_revision":config["revision"],"tokenizer_revision":config["revision"],
        "model_path":str(repo_path(config["model_dir"])),
        "tokenizer_sha256":checkpoint["tokenizer_sha256"],"template_sha256":checkpoint["template_sha256"],
        "versions":versions,"gpu":gpu,
        "base_url":f'http://{config["host"]}:{config["port"]}/v1',
        "settings":{**{name:config[name] for name in (
            "dtype","quantization","tensor_parallel_size","max_model_len","max_num_seqs","gpu_memory_utilization")},
            "reasoning_parser":"qwen3","language_model_only":True,"generation_config":"vllm",
            "cuda_visible_devices":os.environ.get("CUDA_VISIBLE_DEVICES")},
    }


def package_freeze() -> str:
    return "\n".join(sorted(f"{item.metadata['Name']}=={item.version}" for item in packages.distributions()))+"\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config",default="vllm/server.example.json")
    parser.add_argument("--dry-run",action="store_true")
    parser.add_argument("--preflight",action="store_true")
    args = parser.parse_args()
    config = read_config(args.config)
    if args.dry_run:
        print(json.dumps({"command":command(config),"environment":cache_environment(create=False),
                          "manifest":str(repo_path(config["manifest"]))},indent=2))
        return
    os.environ.update(cache_environment())
    os.environ.setdefault("CUDA_VISIBLE_DEVICES",config["cuda_visible_devices"])
    manifest = preflight(config)
    if args.preflight:
        print(json.dumps(manifest,indent=2))
        return
    # Never attach to or stop an unrelated service already using this port.
    with socket.socket() as listener:
        listener.bind((config["host"],config["port"]))
    path = repo_path(config["manifest"])
    path.parent.mkdir(parents=True,exist_ok=True)
    freeze = package_freeze()
    (path.parent/"server_packages.txt").write_text(freeze,encoding="utf-8")
    manifest["started_at"] = datetime.now(timezone.utc).isoformat()
    temporary = path.with_suffix(".tmp")
    temporary.write_text(json.dumps(manifest,indent=2)+"\n",encoding="utf-8")
    temporary.replace(path)
    log = repo_path(config["log"])
    log.parent.mkdir(parents=True,exist_ok=True)
    print("Starting vLLM; server manifest: "+str(path),flush=True)
    print("Server log: "+str(log),flush=True)
    with log.open("a",encoding="utf-8") as stream:
        os.dup2(stream.fileno(),sys.stdout.fileno())
        os.dup2(stream.fileno(),sys.stderr.fileno())
    os.chdir(ROOT)
    os.execvpe(sys.executable,command(config),os.environ)


if __name__ == "__main__":
    main()
