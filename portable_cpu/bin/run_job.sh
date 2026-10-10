#!/usr/bin/env bash
# Run one manifest job (with logging).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

JOB_ID="${1:?Usage: run_job.sh JOB_ID}"
RESUME=""
[[ "${2:-}" == "--resume" ]] && RESUME="--resume"

if [[ ! -x portable_cpu/.venv/bin/python ]]; then
  echo "Run setup first: bash portable_cpu/bin/setup_ubuntu.sh" >&2
  exit 1
fi

portable_cpu/.venv/bin/python portable_cpu/lib/job_runner.py run --job "$JOB_ID" $RESUME
