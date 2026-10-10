#!/usr/bin/env python3
"""Search gap patterns where standard GenericDecomp bags likely need a hub vertex.

Heuristic: simulate fin-graph edge cover with junction bags; flag when overlap
edges fail preconnected under standard adjacency (card ≤ max_bag_card).
"""

from __future__ import annotations

import argparse
import itertools
import json
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PORTABLE = ROOT / "portable_cpu"
STATE_DIR = PORTABLE / "state" / "checkpoints"


def checkpoint_path(job_id: str) -> Path:
    return STATE_DIR / f"{job_id}.json"


def gap_patterns(n: int, max_gap_sum: int):
    for a in range(1, n - 2):
        for b in range(1, n - a - 1):
            for c in range(1, n - a - b):
                d = n - a - b - c
                if d < 1:
                    continue
                if a + b + c + d > max_gap_sum:
                    continue
                yield (0, a, a + b, a + b + c), (a, b, c, d)


def simulate_needs_hub(gaps: tuple[int, int, int, int], max_bag_card: int = 4) -> dict:
    """Toy model: four arc segments; junction bags at chord endpoints may overlap."""
    a, b, c, d = gaps
    # Arc lengths between consecutive endpoints on cycle
    arc_lens = [a, b, c, d]
    long_arc_idx = arc_lens.index(max(arc_lens))
    # Standard template: one bag per short arc + junction at chord endpoints
    n_bags = 4
    bag_sizes = []
    for i, L in enumerate(arc_lens):
        # edges on arc ~ L (cycle edges) + possible chord at endpoints
        size = min(L + 1, max_bag_card + 1)  # +1 endpoint
        if i == long_arc_idx:
            size = min(L, max_bag_card + 2)
        bag_sizes.append(size)
    max_size = max(bag_sizes)
    # Preconnected failure proxy: long arc > 2 * (max_bag_card - 1)
    preconnected_fail = arc_lens[long_arc_idx] > 2 * (max_bag_card - 1)
    needs_hub = max_size > max_bag_card or preconnected_fail
    return {
        "gaps": list(gaps),
        "long_arc": long_arc_idx,
        "bag_sizes": bag_sizes,
        "max_bag_size": max_size,
        "preconnected_fail_proxy": preconnected_fail,
        "needs_hub": needs_hub,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--job-id", required=True)
    parser.add_argument("--max-n", type=int, default=12)
    parser.add_argument("--max-gap-sum", type=int, default=16)
    parser.add_argument("--max-bag-card", type=int, default=4)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--reset", action="store_true")
    args = parser.parse_args()

    ck_path = checkpoint_path(args.job_id)
    ck = json.loads(ck_path.read_text()) if ck_path.exists() and not args.reset else {
        "last_n": None, "results": []
    }
    start_n = 5 if ck["last_n"] is None else ck["last_n"] + 1
    results = list(ck.get("results", []))
    t0 = time.perf_counter()

    for n in range(start_n, args.max_n + 1):
        for _pts, gaps in gap_patterns(n, args.max_gap_sum):
            for pairing in ("crossing", "nested", "disjoint"):
                sim = simulate_needs_hub(gaps, max_bag_card=args.max_bag_card)
                if sim["needs_hub"]:
                    results.append({"n": n, "pairing": pairing, **sim})
        ck_path.parent.mkdir(parents=True, exist_ok=True)
        ck_path.write_text(
            json.dumps({"last_n": n, "results": results, "elapsed_s": round(time.perf_counter() - t0, 2)}, indent=2)
            + "\n",
            encoding="utf-8",
        )
        print(f"n={n}: flagged {sum(1 for r in results if r['n'] == n)} hub candidates")

    out = args.out if args.out.is_absolute() else ROOT / args.out
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(
            {
                "summary": {
                    "max_n": args.max_n,
                    "max_gap_sum": args.max_gap_sum,
                    "total_flagged": len(results),
                },
                "results": results,
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    print(f"Wrote {out} ({len(results)} flagged)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
