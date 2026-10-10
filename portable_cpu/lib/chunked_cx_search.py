#!/usr/bin/env python3
"""Resumable counterexample search with per-n checkpoint."""

from __future__ import annotations

import argparse
import json
import sys
import time
from dataclasses import asdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
if str(ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(ROOT / "scripts"))

from scripts.chordwidth.search_two_chord_counterexamples import (  # noqa: E402
    InstanceRecord,
    analyze_config,
)
from scripts.verify_chord_treewidth import iter_gap_configs  # noqa: E402

PORTABLE = ROOT / "portable_cpu"
STATE_DIR = PORTABLE / "state" / "checkpoints"


def checkpoint_path(job_id: str) -> Path:
    return STATE_DIR / f"{job_id}.json"


def load_checkpoint(job_id: str) -> dict:
    p = checkpoint_path(job_id)
    if p.exists():
        return json.loads(p.read_text(encoding="utf-8"))
    return {"last_completed_n": None, "counterexamples": [], "total_configs": 0}


def save_checkpoint(job_id: str, data: dict) -> None:
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    checkpoint_path(job_id).write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--job-id", required=True)
    parser.add_argument("--n-lo", type=int, default=5)
    parser.add_argument("--n-hi", type=int, default=20)
    parser.add_argument("--exact-max-nodes", type=int, default=20)
    parser.add_argument("--memory-safe", action="store_true")
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--reset", action="store_true")
    args = parser.parse_args()

    ck = load_checkpoint(args.job_id) if not args.reset else {
        "last_completed_n": None, "counterexamples": [], "total_configs": 0
    }
    start_n = args.n_lo
    if ck.get("last_completed_n") is not None:
        start_n = max(args.n_lo, ck["last_completed_n"] + 1)

    counterexamples: list[dict] = list(ck.get("counterexamples", []))
    total = ck.get("total_configs", 0)
    t0 = time.time()

    for n in range(start_n, args.n_hi + 1):
        for cfg in iter_gap_configs(n):
            rec = analyze_config(
                cfg,
                exact_max_nodes=args.exact_max_nodes,
                memory_safe=args.memory_safe,
            )
            total += 1
            if rec.counterexample:
                counterexamples.append(asdict(rec))
                print(f"COUNTEREXAMPLE n={n}: tw={rec.tw_line} expected={rec.expected_tw}")
                save_checkpoint(
                    args.job_id,
                    {
                        "last_completed_n": n,
                        "counterexamples": counterexamples,
                        "total_configs": total,
                        "status": "REFUTED",
                    },
                )
                out = args.out if args.out.is_absolute() else ROOT / args.out
                out.parent.mkdir(parents=True, exist_ok=True)
                out.write_text(
                    json.dumps(
                        {
                            "summary": {
                                "n_range": [args.n_lo, args.n_hi],
                                "counterexamples_found": len(counterexamples),
                                "conjecture_status": "REFUTED",
                            },
                            "counterexamples": counterexamples,
                        },
                        indent=2,
                    )
                    + "\n",
                    encoding="utf-8",
                )
                return 1

        save_checkpoint(
            args.job_id,
            {
                "last_completed_n": n,
                "counterexamples": counterexamples,
                "total_configs": total,
                "status": "NO_COUNTEREXAMPLE_IN_RANGE_PARTIAL",
                "elapsed_s": round(time.time() - t0, 2),
            },
        )
        print(f"n={n} done, total_configs={total}")

    out = args.out if args.out.is_absolute() else ROOT / args.out
    out.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "summary": {
            "n_range": [args.n_lo, args.n_hi],
            "total_configs": total,
            "counterexamples_found": 0,
            "conjecture_status": "NO_COUNTEREXAMPLE_IN_RANGE",
            "elapsed_seconds": round(time.time() - t0, 2),
        },
        "counterexamples": [],
    }
    out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
