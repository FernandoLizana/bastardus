"""Mass: full Closure_Δ of small bicyclic graphs contains □ (Width ≤ Δ).

Unlike `_width_closure_clauses` (early-exit on empty), this saturates fully
then checks □ ∈ Closure and Lean-sound closedness under normalized resolve.
"""

from __future__ import annotations

import json
from collections import defaultdict
from pathlib import Path

import networkx as nx

from backend.proof_complexity.tseitin_family import GraphInstance, tseitin_cnf
from backend.proof_complexity.width import _norm, resolve

OUT = Path("reports/discovery/bicyclic_full_closure_mass.json")


def full_width_closure(formula, width: int) -> set[tuple[int, ...]]:
    clauses: set[tuple[int, ...]] = set()
    by_lit: dict[int, set[tuple[int, ...]]] = defaultdict(set)

    def add(c: tuple[int, ...]) -> None:
        if c in clauses:
            return
        clauses.add(c)
        for lit in c:
            by_lit[lit].add(c)

    for clause in formula.clauses:
        n = _norm(clause.literals)
        if n is not None and len(n) <= width:
            add(n)
    pending = list(clauses)
    while pending:
        if len(clauses) > 50_000:
            break
        a = pending.pop()
        partners: set[tuple[int, ...]] = set()
        for lit in a:
            partners |= by_lit.get(-lit, set())
        for b in partners:
            if a == b:
                continue
            r = resolve(a, b)
            if r is None or len(r) > width or r in clauses:
                continue
            add(r)
            pending.append(r)
    return clauses


def lean_sound_closed(cl: set[tuple[int, ...]], width: int) -> bool:
    S = [list(c) for c in cl]
    Sset = cl
    maxv = max((abs(x) for c in cl for x in c), default=1)

    def is_taut(R: list[int]) -> bool:
        s = set(R)
        return any(-x in s for x in s if x != 0)

    def strip(C: list[int], p: int) -> list[int]:
        return [l for l in C if l != p and l != -p]

    def resolveOriented(C, D, p):
        if p == 0:
            return None
        if p in C and -p in D:
            R = strip(C, p) + strip(D, p)
            if is_taut(R):
                return None
            n = _norm(R)
            return list(n) if n is not None else None
        return None

    for C in S:
        for D in S:
            for p in range(-maxv - 1, maxv + 2):
                r = resolveOriented(C, D, p)
                if r is None or len(r) > width:
                    continue
                if tuple(r) not in Sset:
                    return False
    return True


def main() -> int:
    ok = fail = 0
    rows: list[dict] = []
    # C_n + one chord (θ-family), denser n≤12
    for n in range(4, 13):
        for a in range(2, n - 1):
            g = nx.cycle_graph(n)
            g.add_edge(0, a)
            if max(d for _, d in g.degree()) > 3:
                continue
            form = tseitin_cnf(
                GraphInstance(
                    g, tuple(1 if i == 0 else 0 for i in range(n)), "B", 0, {}
                )
            )
            delta = max(d for _, d in g.degree())
            cl = full_width_closure(form, delta)
            has_empty = () in cl
            closed_ok = lean_sound_closed(cl, delta) if len(cl) <= 500 else None
            row = {
                "kind": "cycle_plus_chord",
                "n": n,
                "chord": [0, a],
                "delta": delta,
                "closure_size": len(cl),
                "has_empty": has_empty,
                "lean_sound_closed": closed_ok,
                "ok": has_empty and (closed_ok is not False),
            }
            rows.append(row)
            if row["ok"]:
                ok += 1
            else:
                fail += 1
    # two triangles sharing an edge (diamond / K_{2,3}-minor-free bicyclic)
    for base_n in range(4, 8):
        g = nx.cycle_graph(base_n)
        # add both diagonals only if n=4; else add one chord + pendant triangle
        if base_n == 4:
            g.add_edges_from([(0, 2)])  # already covered above
            continue
        # attach second cycle by identifying edge (0,1) with new path of length 2
        tip = base_n
        g.add_node(tip)
        g.add_edges_from([(0, tip), (1, tip)])
        if max(d for _, d in g.degree()) > 3:
            continue
        if g.number_of_edges() - g.number_of_nodes() + 1 != 2:
            continue
        nn = g.number_of_nodes()
        form = tseitin_cnf(
            GraphInstance(
                g, tuple(1 if i == 0 else 0 for i in range(nn)), "B2", 0, {}
            )
        )
        delta = max(d for _, d in g.degree())
        cl = full_width_closure(form, delta)
        has_empty = () in cl
        closed_ok = lean_sound_closed(cl, delta) if len(cl) <= 500 else None
        row = {
            "kind": "cycle_plus_triangle_ear",
            "n": base_n,
            "delta": delta,
            "closure_size": len(cl),
            "has_empty": has_empty,
            "lean_sound_closed": closed_ok,
            "ok": has_empty and (closed_ok is not False),
        }
        rows.append(row)
        if row["ok"]:
            ok += 1
        else:
            fail += 1
    report = {
        "total_ok": ok,
        "total_fail": fail,
        "rows": rows,
        "claim": (
            "Full Closure_Δ of bicyclic samples (C_n+chord n≤12; cycle+triangle ear) "
            "with Δ≤3 unit odd contains □; |Cl|≤500 Lean-sound when checked."
        ),
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(f"wrote {OUT} ok={ok} fail={fail}")
    return 0 if fail == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
