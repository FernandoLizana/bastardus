#!/usr/bin/env python3
"""Exhaustive search for tree decompositions with interval bags on path/fork templates.

Checks running intersection property (RI) for width <= max_bag_card on small shapes
relevant to Route F+A discharge attempts.
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


def path_graph_edges(k: int) -> list[tuple[int, int]]:
    return [(i, i + 1) for i in range(k - 1)]


def fork_graph_edges(k: int) -> list[tuple[int, int]]:
    """Central node 0, path 0-1-2-... and branch 0-(k-1) for k nodes."""
    edges = [(0, i) for i in range(1, k)]
    for i in range(1, k - 2):
        edges.append((i, i + 1))
    return sorted(set(edges))


def build_adj(n: int, edges: list[tuple[int, int]]) -> dict[int, set[int]]:
    adj: dict[int, set[int]] = {i: set() for i in range(n)}
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def ri_holds(bags: list[set[int]], tree_edges: list[tuple[int, int]]) -> bool:
    """Verify RI: for each vertex v, indices of bags containing v induce connected subtree."""
    n_bags = len(bags)
    # Build bag adjacency from tree_edges
    bag_adj: dict[int, set[int]] = {i: set() for i in range(n_bags)}
    for a, b in tree_edges:
        bag_adj[a].add(b)
        bag_adj[b].add(a)

    vertices: set[int] = set()
    for b in bags:
        vertices |= b

    for v in vertices:
        containing = [i for i, b in enumerate(bags) if v in b]
        if not containing:
            return False
        if len(containing) == 1:
            continue
        # BFS from first bag among containing
        start = containing[0]
        target = set(containing)
        seen = {start}
        stack = [start]
        while stack:
            u = stack.pop()
            for w in bag_adj[u]:
                if w in target and w not in seen:
                    seen.add(w)
                    stack.append(w)
        if seen != target:
            return False
    return True


def edge_cover(bags: list[set[int]], edges: list[tuple[int, int]]) -> bool:
    for u, v in edges:
        if not any(u in b and v in b for b in bags):
            return False
    return True


def search_interval_decomp(
    n: int,
    edges: list[tuple[int, int]],
    *,
    max_bag_card: int,
    max_bags: int,
) -> list[dict] | None:
    """Try interval bags [i,j] on vertex line 0..n-1 (path embedding)."""
    solutions = []
    for num_bags in range(1, max_bags + 1):
        intervals = []
        for starts in itertools.product(range(n), repeat=num_bags):
            for ends in itertools.product(range(n), repeat=num_bags):
                bags = []
                ok = True
                for s, e in zip(starts, ends):
                    if s > e:
                        ok = False
                        break
                    bag = set(range(s, e + 1))
                    if len(bag) > max_bag_card:
                        ok = False
                        break
                    bags.append(bag)
                if not ok:
                    continue
                if not edge_cover(bags, edges):
                    continue
                # Tree: path on bags 0-1-2-... is sufficient if RI holds
                tree_edges = [(i, i + 1) for i in range(num_bags - 1)]
                if ri_holds(bags, tree_edges):
                    solutions.append(
                        {
                            "num_bags": num_bags,
                            "bags": [sorted(b) for b in bags],
                            "tree": "path",
                        }
                    )
                    if len(solutions) >= 3:
                        return solutions
    return solutions if solutions else None


def checkpoint_path(job_id: str) -> Path:
    return STATE_DIR / f"{job_id}.json"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--job-id", required=True)
    parser.add_argument("--shape", choices=["path", "fork"], default="path")
    parser.add_argument("--nodes-lo", type=int, default=7)
    parser.add_argument("--nodes-hi", type=int, default=10)
    parser.add_argument("--max-bag-card", type=int, default=4)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--reset", action="store_true")
    args = parser.parse_args()

    ck_path = checkpoint_path(args.job_id)
    ck = json.loads(ck_path.read_text()) if ck_path.exists() and not args.reset else {
        "last_nodes": None, "results": {}
    }
    start_k = args.nodes_lo if ck["last_nodes"] is None else ck["last_nodes"] + 1
    results: dict[str, list] = dict(ck.get("results", {}))
    t0 = time.perf_counter()

    for k in range(start_k, args.nodes_hi + 1):
        edges = path_graph_edges(k) if args.shape == "path" else fork_graph_edges(k)
        sols = search_interval_decomp(
            k, edges, max_bag_card=args.max_bag_card, max_bags=min(6, k)
        )
        key = f"{args.shape}_{k}"
        results[key] = {
            "nodes": k,
            "edges": edges,
            "solutions_found": len(sols) if sols else 0,
            "sample": sols[:2] if sols else None,
            "ri_possible": sols is not None and len(sols) > 0,
        }
        ck_path.parent.mkdir(parents=True, exist_ok=True)
        ck_path.write_text(
            json.dumps({"last_nodes": k, "results": results, "elapsed_s": round(time.perf_counter() - t0, 2)}, indent=2)
            + "\n",
            encoding="utf-8",
        )
        print(f"{args.shape} k={k}: RI solutions={results[key]['solutions_found']}")

    out = args.out if args.out.is_absolute() else ROOT / args.out
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({"shape": args.shape, "results": results}, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
