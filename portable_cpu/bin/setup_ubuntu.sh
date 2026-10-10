#!/usr/bin/env bash
# One-time setup on Ubuntu: venv, Python deps, optional Elan check.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

echo "[setup] repo root: $ROOT"

if ! command -v python3 >/dev/null 2>&1; then
  echo "python3 required" >&2
  exit 1
fi

python3 -m venv portable_cpu/.venv
portable_cpu/.venv/bin/pip install -U pip wheel
portable_cpu/.venv/bin/pip install -r portable_cpu/requirements.txt

mkdir -p portable_cpu/logs portable_cpu/state/jobs portable_cpu/state/checkpoints portable_cpu/results experiments

if command -v lake >/dev/null 2>&1; then
  echo "[setup] Lean/Lake found: $(lake --version 2>/dev/null || true)"
else
  echo "[setup] WARNING: lake not in PATH. Install Elan + Lean 4 for lean_* jobs."
  echo "  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y"
fi

echo "[setup] Done. Next:"
echo "  bash portable_cpu/bin/run_all.sh --resume"
