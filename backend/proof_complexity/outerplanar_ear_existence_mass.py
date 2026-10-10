"""Mass: 2-core outerplanar Δ≤3 non-cycles always admit a fold tip (earLaw E2).

Matches TERMINATION.md / Outerplanar.lean `earLaw`: triangle ear or deg-2
adjacent to deg≥3. Samples: C_n + noncrossing ears, nested ears, triangle cacti.
"""

from __future__ import annotations

import json
from itertools import combinations
from pathlib import Path

import networkx as nx

from backend.proof_complexity.outerplanar_pathfold_certs import is_outerplanar

OUT = Path("reports/discovery/outerplanar_ear_existence_mass.json")
OUT_N12 = Path("reports/discovery/outerplanar_ear_existence_mass_n12.json")
OUT_N14 = Path("reports/discovery/outerplanar_ear_existence_mass_n14.json")


def peel_trees(g: nx.Graph) -> nx.Graph:
    work = g.copy()
    changed = True
    while changed:
        changed = False
        leaves = [v for v, d in work.degree() if d == 1]
        for leaf in leaves:
            if work.number_of_nodes() <= 2:
                break
            work.remove_node(leaf)
            changed = True
    return work


def is_pure_cycle(g: nx.Graph) -> bool:
    return (
        g.number_of_nodes() >= 3
        and g.number_of_edges() == g.number_of_nodes()
        and nx.is_connected(g)
        and all(d == 2 for _, d in g.degree())
    )


def has_triangle_ear(g: nx.Graph) -> bool:
    for v, d in g.degree():
        if d != 2:
            continue
        u, w = list(g.neighbors(v))
        if g.has_edge(u, w):
            return True
    return False


def has_shortcut_tip(g: nx.Graph) -> bool:
    for v, d in g.degree():
        if d != 2:
            continue
        u, w = list(g.neighbors(v))
        if g.degree(u) >= 3 or g.degree(w) >= 3:
            return True
    return False


def check_core(g: nx.Graph) -> dict:
    core = peel_trees(g)
    if core.number_of_nodes() < 3 or not nx.is_connected(core):
        return {"ok": True, "kind": "degenerate_after_peel"}
    if is_pure_cycle(core):
        return {"ok": True, "kind": "cycle", "n": core.number_of_nodes()}
    tri = has_triangle_ear(core)
    sh = has_shortcut_tip(core)
    return {
        "ok": tri or sh,
        "kind": "needs_fold",
        "triangle": tri,
        "shortcut": sh,
        "n": core.number_of_nodes(),
        "m": core.number_of_edges(),
        "degs": sorted(d for _, d in core.degree()),
    }


def sample_graphs(max_n: int = 11) -> list[tuple[str, nx.Graph]]:
    out: list[tuple[str, nx.Graph]] = []
    # ears on cycle (span-2 noncrossing)
    for n in range(4, max_n + 1):
        ears = sorted({tuple(sorted((i, (i + 2) % n))) for i in range(n)})
        kmax = min(5, len(ears))
        for k in range(0, kmax + 1):
            for chords in combinations(ears, k):
                g = nx.cycle_graph(n)
                g.add_edges_from(chords)
                if max(d for _, d in g.degree()) > 3:
                    continue
                if not is_outerplanar(g):
                    continue
                out.append((f"ears_n{n}_k{k}", g))
    # span-3 noncrossing ears (still outerplanar when noncrossing)
    for n in range(6, min(max_n, 12) + 1):
        ears3 = sorted({tuple(sorted((i, (i + 3) % n))) for i in range(n // 2)})
        for k in range(0, min(3, len(ears3) + 1)):
            for chords in combinations(ears3, k):
                g = nx.cycle_graph(n)
                g.add_edges_from(chords)
                if max(d for _, d in g.degree()) > 3:
                    continue
                if not is_outerplanar(g):
                    continue
                out.append((f"span3_n{n}_k{k}", g))
    # nested / chain of triangles (cactus)
    for t in range(1, 12):
        g = nx.Graph()
        for i in range(t):
            a, b, c = i, i + 1, 100 + i
            g.add_edges_from([(a, b), (b, c), (c, a)])
        if max(d for _, d in g.degree()) > 3:
            continue
        if is_outerplanar(g):
            out.append((f"tri_cactus_{t}", g))
    # fan: triangle glued on edge (0,1) of cycle
    for n in range(5, min(max_n, 10) + 1):
        g = nx.cycle_graph(n)
        g.add_node(n)
        g.add_edges_from([(0, n), (1, n)])
        if max(d for _, d in g.degree()) > 3:
            continue
        if is_outerplanar(g):
            out.append((f"fan_tri_n{n}", g))
    return out


def main() -> int:
    ok = fail = 0
    fails: list[dict] = []
    by_kind: dict[str, int] = {}
    max_n = 14
    for label, g in sample_graphs(max_n):
        cert = check_core(g)
        by_kind[cert["kind"]] = by_kind.get(cert["kind"], 0) + 1
        if cert["ok"]:
            ok += 1
        else:
            fail += 1
            if len(fails) < 20:
                fails.append({"label": label, **cert})
    report = {
        "total_ok": ok,
        "total_fail": fail,
        "by_kind": by_kind,
        "fails": fails,
        "max_n": max_n,
        "claim": (
            "After tree peel, every sampled connected outerplanar Δ≤3 residual that "
            "is not a cycle has a triangle ear or a deg-2 tip next to deg≥3 "
            "(earLaw combinatorial content)."
        ),
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2), encoding="utf-8")
    OUT_N12.write_text(json.dumps(report, indent=2), encoding="utf-8")
    OUT_N14.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(f"wrote {OUT} ok={ok} fail={fail} by_kind={by_kind}")
    return 0 if fail == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
