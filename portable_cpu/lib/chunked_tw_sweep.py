#!/usr/bin/env python3
"""Resumable treewidth sweep: one checkpoint per n, append CSV incrementally."""

from __future__ import annotations

import argparse
import csv
import json
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
if str(ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(ROOT / "scripts"))

from scripts.verify_chord_treewidth import (  # noqa: E402
    analyze_config,
    iter_configs,
    write_csv,
)

PORTABLE = ROOT / "portable_cpu"
STATE_DIR = PORTABLE / "state" / "checkpoints"

CSV_FIELDS = [
    "n", "p0", "p1", "p2", "p3", "pairing", "gap_pattern", "chord_spec",
    "crosses", "delta", "tw_line_graph", "tw_expected", "match", "tw_method",
    "line_graph_order",
]


def checkpoint_path(job_id: str) -> Path:
    return STATE_DIR / f"{job_id}.json"


def load_checkpoint(job_id: str) -> dict:
    p = checkpoint_path(job_id)
    if p.exists():
        return json.loads(p.read_text(encoding="utf-8"))
    return {"last_completed_n": None, "total_rows": 0, "mismatches": 0}


def save_checkpoint(job_id: str, data: dict) -> None:
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    checkpoint_path(job_id).write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")


def append_rows(csv_path: Path, rows: list[dict], *, write_header: bool) -> None:
    csv_path.parent.mkdir(parents=True, exist_ok=True)
    mode = "w" if write_header else "a"
    with csv_path.open(mode, newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=CSV_FIELDS)
        if write_header:
            w.writeheader()
        w.writerows(rows)


def filter_configs(configs, pairing_filter: str | None):
    if pairing_filter is None:
        return configs
    if pairing_filter == "crossing":
        return [c for c in configs if c.pairing == "crossing"]
    if pairing_filter == "noncrossing":
        return [c for c in configs if c.pairing in ("nested", "disjoint")]
    raise ValueError(f"unknown pairing_filter {pairing_filter!r}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--job-id", required=True)
    parser.add_argument("--n-lo", type=int, default=5)
    parser.add_argument("--n-hi", type=int, default=14)
    parser.add_argument("--exact-max-nodes", type=int, default=14)
    parser.add_argument("--memory-safe", action="store_true")
    parser.add_argument("--no-memory-safe", action="store_true")
    parser.add_argument("--full-endpoints", action="store_true")
    parser.add_argument("--representative", action="store_true")
    parser.add_argument("--no-representative", action="store_true")
    parser.add_argument("--pairing-filter", choices=["crossing", "noncrossing"], default=None)
    parser.add_argument("--csv", type=Path, required=True)
    parser.add_argument("--reset", action="store_true", help="Ignore checkpoint and restart")
    args = parser.parse_args()

    memory_safe = True
    if args.no_memory_safe:
        memory_safe = False
    elif args.memory_safe:
        memory_safe = True

    representative = True
    if args.no_representative:
        representative = False
    elif args.representative:
        representative = True

    ck = {"last_completed_n": None, "total_rows": 0, "mismatches": 0}
    if not args.reset:
        ck = load_checkpoint(args.job_id)

    start_n = args.n_lo
    if ck["last_completed_n"] is not None:
        start_n = max(args.n_lo, ck["last_completed_n"] + 1)

    csv_path = args.csv if args.csv.is_absolute() else ROOT / args.csv
    write_header = not csv_path.exists() or args.reset or ck["last_completed_n"] is None
    if args.reset and csv_path.exists():
        csv_path.unlink()

    total_mismatches = ck.get("mismatches", 0)
    total_rows = ck.get("total_rows", 0)
    t0 = time.perf_counter()

    for n in range(start_n, args.n_hi + 1):
        configs = iter_configs(
            n,
            exhaustive_endpoints=args.full_endpoints,
            representative=representative,
        )
        configs = filter_configs(configs, args.pairing_filter)
        rows = []
        skipped = 0
        for cfg in configs:
            row = analyze_config(cfg, exact_max_nodes=args.exact_max_nodes, memory_safe=memory_safe)
            if row is None:
                skipped += 1
                continue
            rows.append(row)
            if not row["match"] and row.get("tw_method") != "timeout":
                total_mismatches += 1

        append_rows(csv_path, rows, write_header=write_header)
        write_header = False
        total_rows += len(rows)
        save_checkpoint(
            args.job_id,
            {
                "last_completed_n": n,
                "total_rows": total_rows,
                "mismatches": total_mismatches,
                "skipped_last_n": skipped,
                "elapsed_s": round(time.perf_counter() - t0, 2),
            },
        )
        print(f"n={n}: {len(rows)} rows (skipped {skipped}), total={total_rows}, mismatches={total_mismatches}")

    print(f"Done. CSV: {csv_path}")
    return 1 if total_mismatches else 0


if __name__ == "__main__":
    raise SystemExit(main())
