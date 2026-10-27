"""Download the pinned checkpoint; all data stays under ITPEval/vllm."""

from __future__ import annotations

import argparse
import json
import os

from settings import cache_environment, metadata_hashes, read_config, repo_path, verify_checkpoint


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config",default="vllm/server.example.json")
    parser.add_argument("--check",action="store_true",help="Validate an existing download without network access.")
    args = parser.parse_args()
    config = read_config(args.config)
    os.environ.update(cache_environment())
    if args.check:
        verify_checkpoint(config)
        print("Pinned checkpoint and tokenizer metadata verified.")
        return
    from huggingface_hub import HfApi, snapshot_download
    info = HfApi().model_info(config["model"],revision=config["revision"])
    if info.sha!=config["revision"]:
        raise ValueError("Hugging Face did not resolve the pinned checkpoint commit")
    directory = repo_path(config["model_dir"])
    previous = directory/".itpeval_download.json"
    if previous.is_file():
        old = json.loads(previous.read_text(encoding="utf-8"))
        if old.get("model")!=config["model"] or old.get("revision")!=config["revision"]:
            raise ValueError("choose a fresh model_dir for a different checkpoint revision")
    directory.mkdir(parents=True,exist_ok=True)
    snapshot_download(repo_id=config["model"],revision=config["revision"],local_dir=str(directory))
    files = {
        str(path.relative_to(directory)).replace(os.sep,"/"):path.stat().st_size
        for path in directory.rglob("*") if path.is_file()
        and ".cache" not in path.relative_to(directory).parts
        and path.name not in {".itpeval_download.json",".itpeval_download.tmp"}
    }
    manifest = {"schema_version":"itpeval_checkpoint_v1","model":config["model"],
                "revision":config["revision"],"files":files,**metadata_hashes(directory)}
    temporary = directory/".itpeval_download.tmp"
    temporary.write_text(json.dumps(manifest,indent=2)+"\n",encoding="utf-8")
    temporary.replace(directory/".itpeval_download.json")
    verify_checkpoint(config)
    print("Downloaded pinned checkpoint to "+str(directory))


if __name__ == "__main__":
    main()
