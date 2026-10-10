#!/usr/bin/env bash
# Run all pending portable_cpu jobs (respects dependencies + parallel groups).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

RESUME=""
PROFILE=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --resume) RESUME="--resume"; shift ;;
    --profile)
      PROFILE="$2"
      shift 2
      ;;
    *) echo "Unknown: $1" >&2; exit 1 ;;
  esac
done

if [[ "$PROFILE" == "high_ram" ]]; then
  # shellcheck source=/dev/null
  source "$ROOT/portable_cpu/profiles/high_ram.env"
  NPROC=$(($(nproc 2>/dev/null || echo 8) - 1))
  [[ "$NPROC" -lt 1 ]] && NPROC=1
  if [[ "${PORTABLE_CPU_JOBS:-6}" == "6" ]]; then
    export PORTABLE_CPU_JOBS=$(( NPROC > 6 ? NPROC : 6 ))
  fi
elif [[ -z "${PORTABLE_CPU_JOBS:-}" ]]; then
  export PORTABLE_CPU_JOBS=$(($(nproc 2>/dev/null || echo 4) - 1))
fi

export PORTABLE_CPU_JOBS="${PORTABLE_CPU_JOBS:-1}"
[[ "$PORTABLE_CPU_JOBS" -lt 1 ]] && PORTABLE_CPU_JOBS=1

if [[ ! -x portable_cpu/.venv/bin/python ]]; then
  echo "[run_all] venv missing — running setup..."
  bash portable_cpu/bin/setup_ubuntu.sh
fi

echo "[run_all] profile=${PROFILE:-default} PORTABLE_CPU_JOBS=$PORTABLE_CPU_JOBS"
if [[ -n "${PORTABLE_CPU_EXTRA_MANIFEST:-}" ]]; then
  echo "[run_all] extra manifest=$PORTABLE_CPU_EXTRA_MANIFEST"
fi
portable_cpu/.venv/bin/python portable_cpu/lib/job_runner.py status
echo "---"
portable_cpu/.venv/bin/python portable_cpu/lib/job_runner.py run $RESUME --max-parallel "$PORTABLE_CPU_JOBS"
