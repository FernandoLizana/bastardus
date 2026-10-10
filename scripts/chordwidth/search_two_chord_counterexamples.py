#!/usr/bin/env python3
"""Adversarial counterexample search for tw(L(G)) dichotomy on CycleTwoChordGraph.

Conjecture under test (non-degenerate, max degree 3):
  noncrossing (nested|disjoint) => tw(L(G)) = 3
  crossing => tw(L(G)) = 4

Does NOT claim proof on success — only reports search bounds and any counterexample.

Usage:
  PYTHONPATH=scripts python scripts/chordwidth/search_two_chord_counterexamples.py
  PYTHONPATH=scripts python scripts/chordwidth/search_two_chord_counterexamples.py --n-hi 14 --exact
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
import time
from dataclasses import asdict, dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
if str(ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(ROOT / "scripts"))

from scripts.verify_chord_treewidth import (  # noqa: E402
    ChordConfig,
    build_graph,
    iter_gap_configs,
)
from treewidth import compute_treewidth, treewidth_lower_bound  # noqa: E402
from treewidth.decomp import verify_certificate, elimination_order_for_path_certificate  # noqa: E402
from treewidth.decomp import elimination_to_path_decomp, _canonical_edges  # noqa: E402
import networkx as nx  # noqa: E402

OUT_DIR = ROOT / "experiments" / "chordwidth_counterexamples"
RESULTS_JSON = OUT_DIR / "results.json"
REPRO_JSON = OUT_DIR / "reproducibility.json"

SEED = 20260804


@dataclass
class InstanceRecord:
    n: int
    p0: int
    p1: int
    p2: int
    p3: int
    pairing: str
    crossing: bool
    max_degree: int
    tw_line: int
    tw_method: str
    tw_lb: int
    n_vertices_line: int
    n_edges_line: int
    expected_tw: int
    counterexample: bool
    degenerate: bool


def is_degenerate(cfg: ChordConfig) -> bool:
    return max_degree(build_graph(cfg)) != 3


def max_degree(g: nx.Graph) -> int:
    return max(dict(g.degree()).values()) if g.number_of_nodes() else 0


def line_graph_reindexed_fixed(g: nx.Graph) -> nx.Graph:
    base_edges = _canonical_edges(g)
    idx = {tuple(e): i for i, e in enumerate(base_edges)}

    def remap(edge: tuple[int, int]) -> int:
        u, v = edge
        if u > v:
            u, v = v, u
        return idx[(u, v)]

    lg = nx.line_graph(g)
    lg2 = nx.Graph()
    lg2.add_nodes_from(range(len(base_edges)))
    for u, v in lg.edges():
        lg2.add_edge(remap(u), remap(v))
    return lg2


def analyze_config(cfg: ChordConfig, *, exact_max_nodes: int, memory_safe: bool) -> InstanceRecord:
    g = build_graph(cfg)
    md = max_degree(g)
    degenerate = md != 3
    crossing = cfg.pairing == "crossing"
    expected = 4 if crossing else 3
    if degenerate:
        return InstanceRecord(
            n=cfg.n,
            p0=cfg.p0,
            p1=cfg.p1,
            p2=cfg.p2,
            p3=cfg.p3,
            pairing=cfg.pairing,
            crossing=crossing,
            max_degree=md,
            tw_line=-1,
            tw_method="skipped_degenerate",
            tw_lb=-1,
            n_vertices_line=0,
            n_edges_line=0,
            expected_tw=expected,
            counterexample=False,
            degenerate=True,
        )
    lg = line_graph_reindexed_fixed(g)
    tw, method = compute_treewidth(lg, exact_max_nodes=exact_max_nodes, memory_safe=memory_safe)
    lb = treewidth_lower_bound(lg)
    counter = (not crossing and tw != 3) or (crossing and tw != 4)
    return InstanceRecord(
        n=cfg.n,
        p0=cfg.p0,
        p1=cfg.p1,
        p2=cfg.p2,
        p3=cfg.p3,
        pairing=cfg.pairing,
        crossing=crossing,
        max_degree=md,
        tw_line=tw,
        tw_method=method,
        tw_lb=lb,
        n_vertices_line=lg.number_of_nodes(),
        n_edges_line=lg.number_of_edges(),
        expected_tw=expected,
        counterexample=counter,
        degenerate=False,
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n-lo", type=int, default=5)
    parser.add_argument("--n-hi", type=int, default=14)
    parser.add_argument("--exact", action="store_true", help="Require exact tw methods only.")
    parser.add_argument("--exact-max-nodes", type=int, default=20)
    parser.add_argument("--memory-safe", action="store_true")
    args = parser.parse_args()

    t0 = time.time()
    records: list[InstanceRecord] = []
    counterexamples: list[InstanceRecord] = []
    by_branch = {"crossing": 0, "noncrossing": 0, "degenerate": 0}

    for n in range(args.n_lo, args.n_hi + 1):
        for cfg in iter_gap_configs(n):
            rec = analyze_config(
                cfg,
                exact_max_nodes=args.exact_max_nodes,
                memory_safe=args.memory_safe,
            )
            records.append(rec)
            if rec.degenerate:
                by_branch["degenerate"] += 1
            elif rec.crossing:
                by_branch["crossing"] += 1
            else:
                by_branch["noncrossing"] += 1
            if rec.counterexample:
                counterexamples.append(rec)
                print(f"COUNTEREXAMPLE: n={rec.n} {rec.pairing} tw={rec.tw_line} expected={rec.expected_tw}")
                break
        if counterexamples:
            break

    elapsed = time.time() - t0
    valid = [r for r in records if not r.degenerate]
    exact_methods = {
        "exact_bruteforce",
        "exact_width_search",
        "exact_confirmed",
    }
    non_exact = [r for r in valid if r.tw_method not in exact_methods]

    summary = {
        "seed": SEED,
        "n_range": [args.n_lo, args.n_hi],
        "total_configs": len(records),
        "valid_configs": len(valid),
        "degenerate_configs": by_branch["degenerate"],
        "crossing_valid": sum(1 for r in valid if r.crossing),
        "noncrossing_valid": sum(1 for r in valid if not r.crossing),
        "counterexamples_found": len(counterexamples),
        "non_exact_tw_count": len(non_exact),
        "elapsed_seconds": round(elapsed, 2),
        "conjecture_status": "REFUTED" if counterexamples else "NO_COUNTEREXAMPLE_IN_RANGE",
    }

    OUT_DIR.mkdir(parents=True, exist_ok=True)
    payload = {
        "summary": summary,
        "counterexamples": [asdict(c) for c in counterexamples],
        "records_hash": hashlib.sha256(
            json.dumps([asdict(r) for r in records], sort_keys=True).encode()
        ).hexdigest(),
    }
    RESULTS_JSON.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    REPRO_JSON.write_text(
        json.dumps(
            {
                "script": "scripts/chordwidth/search_two_chord_counterexamples.py",
                "argv": sys.argv,
                "summary": summary,
                "results_file": str(RESULTS_JSON.relative_to(ROOT)),
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )

    print(json.dumps(summary, indent=2))
    print(f"Wrote {RESULTS_JSON.relative_to(ROOT)}")
    return 1 if counterexamples else 0


if __name__ == "__main__":
    raise SystemExit(main())
