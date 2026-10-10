#!/usr/bin/env bash
# Resumable lake build for PNPLab.ChordWidth.Main (Ubuntu).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
LEAN_DIR="$ROOT/lean"
LOG="$LEAN_DIR/build-chordwidth-resume.log"
STATE="$ROOT/portable_cpu/state/lean_chordwidth_build.json"
LOCK="$ROOT/portable_cpu/state/.lean_chordwidth.lock"

MAX_ATTEMPTS="${MAX_ATTEMPTS:-0}"
RETRY_DELAY="${RETRY_DELAY_SEC:-120}"
LEAN_THREADS="${LEAN_THREADS:-0}"
CACHE_ONLY=false

while [[ $# -gt 0 ]]; do
  case "$1" in
    --cache-only) CACHE_ONLY=true; shift ;;
    --threads) LEAN_THREADS="$2"; shift 2 ;;
    *) echo "Unknown: $1" >&2; exit 1 ;;
  esac
done

log() { echo "[$(date '+%Y-%m-%d %H:%M:%S')] $*" | tee -a "$LOG"; }

acquire_lock() {
  mkdir -p "$(dirname "$LOCK")"
  if [[ -f "$LOCK" ]]; then
    pid="$(cat "$LOCK" 2>/dev/null || true)"
    if [[ -n "$pid" ]] && kill -0 "$pid" 2>/dev/null; then
      log "Another lean build running (pid $pid). Exit."
      exit 2
    fi
    rm -f "$LOCK"
  fi
  echo $$ > "$LOCK"
}

release_lock() { rm -f "$LOCK"; }
trap release_lock EXIT

stop_lean() {
  pkill -9 lean 2>/dev/null || true
  pkill -9 lake 2>/dev/null || true
  sleep 3
}

save_state() {
  python3 - <<PY
import json, pathlib
path = pathlib.Path("$STATE")
path.parent.mkdir(parents=True, exist_ok=True)
path.write_text(json.dumps($1, indent=2) + "\n")
PY
}

acquire_lock
mkdir -p "$(dirname "$LOG")"
cd "$LEAN_DIR"

if $CACHE_ONLY; then
  log "lake exe cache get..."
  lake exe cache get 2>&1 | tee -a "$LOG"
  save_state '{"status":"cache_ok"}'
  exit 0
fi

attempt=0
while true; do
  attempt=$((attempt + 1))
  if [[ "$MAX_ATTEMPTS" -gt 0 && "$attempt" -gt "$MAX_ATTEMPTS" ]]; then
    log "Max attempts reached."
    save_state "{\"status\":\"failed\",\"attempts\":$attempt}"
    exit 1
  fi
  stop_lean
  log "Attempt $attempt: lake build PNPLab.ChordWidth.Main (threads=$LEAN_THREADS)"
  save_state "{\"status\":\"running\",\"attempts\":$attempt}"
  set +e
  if [[ "$LEAN_THREADS" -gt 0 ]]; then
    lake build PNPLab.ChordWidth.Main -j"$LEAN_THREADS" 2>&1 | tee -a "$LOG"
  else
    lake build PNPLab.ChordWidth.Main 2>&1 | tee -a "$LOG"
  fi
  code=$?
  set -e
  if [[ $code -eq 0 ]]; then
    log "Build GREEN."
    save_state "{\"status\":\"success\",\"attempts\":$attempt}"
    exit 0
  fi
  log "Build failed (exit $code). Retry in ${RETRY_DELAY}s..."
  save_state "{\"status\":\"retry\",\"attempts\":$attempt,\"last_exit\":$code}"
  sleep "$RETRY_DELAY"
done
