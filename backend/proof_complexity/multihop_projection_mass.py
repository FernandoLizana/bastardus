"""Mass multi-hop projection: each path-fold tip preserves Closure₃ inclusion.

For every crossing C_n+2 (Δ≤3 odd charge), fold deg-2 tips tip-by-tip along
open arcs and check that supported clauses of Closure₃(G_i) sit in
Closure₃(G_{i+1}). Final residual must be size-16 K₄ XOR closure without □.
"""

from __future__ import annotations

import json
from itertools import combinations
from pathlib import Path

import networkx as nx

from backend.models.cnf import CNFFormula
from backend.proof_complexity.chord_crossing_law import chords_cross_on_cycle
from backend.proof_complexity.constructive_proofs import (
    _ProofBuilder,
    _all_axioms,
    _edge_var_map,
    _xor_clauses_for_vertex,
)
from backend.proof_complexity.k4_minor_lower_bound import crossing_branch_sets
from backend.proof_complexity.k4_path_contraction_derivation import _odd_charge_for_crossing
from backend.proof_complexity.k4_projection_restriction import _width_closure_clauses
from backend.proof_complexity.path_fold import fold_deg2_tip
from backend.proof_complexity.width import _norm

OUT = Path("reports/discovery/multihop_projection_mass.json")


def _xor_axioms(work, charges, e_index) -> list[tuple[int, ...]]:
    axs: list[tuple[int, ...]] = []
    for v in work.nodes():
        for raw in _xor_clauses_for_vertex(work, e_index, v, charges[v]):
            n = _norm(raw)
            if n is not None and n not in axs:
                axs.append(n)
    return axs


def _edge_vars(work, e_index) -> set[int]:
    return {
        e_index[tuple(sorted(e))]
        for e in work.edges()
        if tuple(sorted(e)) in e_index
    }


def _closure(axioms: list[tuple[int, ...]]) -> set[tuple[int, ...]]:
    form = CNFFormula.from_clauses(
        [list(c) for c in axioms],
        num_variables=max((abs(lit) for c in axioms for lit in c), default=1),
    )
    return _width_closure_clauses(form, 3)


def check_multihop(n: int, c1: tuple[int, int], c2: tuple[int, int]) -> dict:
    charges0 = _odd_charge_for_crossing(n, c1, c2)
    g0 = nx.cycle_graph(n)
    g0.add_edges_from([c1, c2])
    ends, arcs = crossing_branch_sets(n, c1, c2)
    e_index = _edge_var_map(g0)
    builder = _ProofBuilder(
        _all_axioms(g0, charges0, e_index),
        delta=max(d for _, d in g0.degree()),
    )
    work = g0.copy()
    charges = dict(charges0)

    prev = _closure(_xor_axioms(work, charges, e_index))
    hop_sizes = [len(prev)]
    miss_total = 0
    tips = 0

    for i, arc in enumerate(arcs):
        path = list(arc)
        while path:
            tip = path.pop(0)
            fold_deg2_tip(builder, work, charges, e_index, tip)
            tips += 1
            cur = _closure(_xor_axioms(work, charges, e_index))
            vv = _edge_vars(work, e_index)
            missing = [
                c
                for c in prev
                if c and all(abs(lit) in vv for lit in c) and c not in cur
            ]
            miss_total += len(missing)
            hop_sizes.append(len(cur))
            prev = cur

    return {
        "n": n,
        "chords": [list(c1), list(c2)],
        "tips": tips,
        "hop_sizes": hop_sizes,
        "missing": miss_total,
        "final_size": hop_sizes[-1],
        "empty_final": () in prev,
        "ok": miss_total == 0 and () not in prev and hop_sizes[-1] == 16,
    }


def chord_pairs(n: int):
    chords = [
        c
        for c in combinations(range(n), 2)
        if (c[1] - c[0]) % n not in (1, n - 1)
    ]
    for c1, c2 in combinations(chords, 2):
        if len(set(c1) | set(c2)) < 4:
            continue
        if chords_cross_on_cycle(n, c1, c2):
            yield c1, c2


def main() -> int:
    ok = 0
    fail = 0
    fails: list[dict] = []
    by_n: dict[str, dict] = {}
    max_tips = 0
    for n in range(5, 11):
        n_ok = n_fail = 0
        for c1, c2 in chord_pairs(n):
            cert = check_multihop(n, c1, c2)
            max_tips = max(max_tips, cert["tips"])
            if cert["ok"]:
                ok += 1
                n_ok += 1
            else:
                fail += 1
                n_fail += 1
                if len(fails) < 20:
                    fails.append(cert)
        by_n[str(n)] = {"ok": n_ok, "fail": n_fail}
    report = {
        "total_ok": ok,
        "total_fail": fail,
        "by_n": by_n,
        "max_tips": max_tips,
        "fails": fails,
        "claim": (
            "Tip-by-tip path-fold multihop: supported Closure₃(G_i) ⊆ Closure₃(G_{i+1}); "
            "final residual Closure₃ size 16 without □ (n=5..10 crossings)."
        ),
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(f"wrote {OUT} ok={ok} fail={fail} by_n={by_n} max_tips={max_tips}")
    return 0 if fail == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
