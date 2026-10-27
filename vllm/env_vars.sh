#!/usr/bin/env bash
# Source from the repository root before conda/pip/download/serve commands.
ITPEVAL_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
export ITPEVAL_ROOT
export CONDA_PKGS_DIRS="$ITPEVAL_ROOT/vllm/cache/conda"
export PIP_CACHE_DIR="$ITPEVAL_ROOT/vllm/cache/pip"
export HF_HOME="$ITPEVAL_ROOT/vllm/cache/huggingface"
export HF_HUB_CACHE="$HF_HOME/hub"
export XDG_CACHE_HOME="$ITPEVAL_ROOT/vllm/cache/xdg"
export TORCH_HOME="$ITPEVAL_ROOT/vllm/cache/torch"
export TORCHINDUCTOR_CACHE_DIR="$ITPEVAL_ROOT/vllm/cache/torchinductor"
export TRITON_CACHE_DIR="$ITPEVAL_ROOT/vllm/cache/triton"
export VLLM_CACHE_ROOT="$ITPEVAL_ROOT/vllm/cache/vllm"
export CUDA_CACHE_PATH="$ITPEVAL_ROOT/vllm/cache/cuda"
export TMPDIR="$ITPEVAL_ROOT/vllm/cache/tmp"
export TMP="$TMPDIR"
export TEMP="$TMPDIR"
mkdir -p -- "$CONDA_PKGS_DIRS" "$PIP_CACHE_DIR" "$HF_HOME" "$HF_HUB_CACHE" \
  "$XDG_CACHE_HOME" "$TORCH_HOME" "$TORCHINDUCTOR_CACHE_DIR" "$TRITON_CACHE_DIR" \
  "$VLLM_CACHE_ROOT" "$CUDA_CACHE_PATH" "$TMPDIR"
