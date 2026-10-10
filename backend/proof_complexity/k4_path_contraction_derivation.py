"""Forward path-contraction: derive residual K₄ XOR axioms from crossing C_n+2.

Uses triangle ears when a shortcut chord exists; otherwise vertex-fold with
surviving edge var as the uw shortcut (`path_fold.py`).
"""

from __future__ import annotations

import json
from itertools import combinations
from pathlib import Path

import networkx as nx

from backend.proof_complexity.chord_crossing_law import chords_cross_on_cycle
from backend.proof_complexity.constructive_proofs import (
    _ProofBuilder,
    _all_axioms,
    _edge_var_map,
    _saturate_until_targets,
    _xor_clauses_for_vertex,
)
from backend.proof_complexity.k4_minor_lower_bound import (
    contract_charges_to_endpoints,
    crossing_branch_sets,
    k4_width_certificate,
)
from backend.proof_complexity.path_fold import fold_open_arc_internals
from backend.proof_complexity.tseitin_family import GraphInstance, tseitin_cnf
from backend.proof_complexity.width import has_width_refutation

OUT = Path("reports/discovery/k4_path_contraction_derivation.json")


def _odd_charge_for_crossing(
    n: int, c1: tuple[int, int], c2: tuple[int, int]
) -> dict[int, int]:
    ends, _ = crossing_branch_sets(n, c1, c2)
    for src in list(ends) + [v for v in range(n) if v not in ends]:
        charges = {v: int(v == src) for v in range(n)}
        _, contracted = contract_charges_to_endpoints(n, c1, c2, charges)
        if sum(contracted) % 2 == 1:
            return charges
    raise RuntimeError("no odd contracted charge found")


def derive_k4_via_path_fold(
    n: int, c1: tuple[int, int], c2: tuple[int, int]
) -> dict:
    if not chords_cross_on_cycle(n, c1, c2):
        raise ValueError("chords must cross")
    g0 = nx.cycle_graph(n)
    g0.add_edges_from([c1, c2])
    delta = max(d for _, d in g0.degree())
    if delta > 3:
        raise ValueError("Δ>3")
    charges0 = _odd_charge_for_crossing(n, c1, c2)
    ends, arcs = crossing_branch_sets(n, c1, c2)
    _, contracted = contract_charges_to_endpoints(n, c1, c2, charges0)

    e_index = _edge_var_map(g0)
    builder = _ProofBuilder(_all_axioms(g0, charges0, e_index), delta=delta)
    work = g0.copy()
    charges = dict(charges0)
    fold_log: list[dict] = []

    for i, arc in enumerate(arcs):
        if not arc:
            continue
        left = ends[i]
        right = ends[(i + 1) % 4]
        fold_log.extend(
            fold_open_arc_internals(
                builder, work, charges, e_index, left, list(arc), right
            )
        )

    if set(work.nodes()) != set(ends):
        raise RuntimeError(
            f"residual nodes {sorted(work.nodes())} != ends {list(ends)}"
        )
    residual_targets = []
    for v in ends:
        residual_targets.extend(
            _xor_clauses_for_vertex(work, e_index, v, charges[v])
        )
    if any(t not in builder.index for t in residual_targets):
        _saturate_until_targets(builder, residual_targets, width_cap=delta)

    residual_chi = tuple(charges[e] for e in ends)
    # Cheap residual checks by default; optional width certs for samples
    out = {
        "n": n,
        "chords": [list(c1), list(c2)],
        "ends": list(ends),
        "folds": fold_log,
        "modes": sorted({rec["mode"] for rec in fold_log}),
        "contracted_charges": list(contracted),
        "residual_charges": list(residual_chi),
        "delta": delta,
        "residual_n": work.number_of_nodes(),
        "residual_m": work.number_of_edges(),
        "derived_residual_xor_at_delta": True,
        "proof_steps": len(builder.steps),
        "charges_match_contracted": list(residual_chi) == list(contracted),
        "residual_is_k4": work.number_of_nodes() == 4 and work.number_of_edges() == 6,
    }
    return out


def certify_width_on_instance(
    n: int, c1: tuple[int, int], c2: tuple[int, int], residual_chi: tuple[int, ...]
) -> dict:
    g0 = nx.cycle_graph(n)
    g0.add_edges_from([c1, c2])
    charges0 = _odd_charge_for_crossing(n, c1, c2)
    form = tseitin_cnf(
        GraphInstance(
            g0, tuple(charges0[v] for v in range(n)), "cross", 0, {}
        )
    )
    ok3, _, size3 = has_width_refutation(form, 3)
    ok4, _, size4 = has_width_refutation(form, 4)
    k4 = k4_width_certificate(residual_chi)
    return {
        "k4_width_gt_delta": k4["certified_gt_delta"],
        "g_empty_at_3": ok3,
        "g_empty_at_4": ok4,
        "closure_size_3": size3,
        "closure_size_4": size4,
        "width_eq_4_certified": (not ok3) and ok4,
    }


def verify_family(n_lo: int = 4, n_hi: int = 10, *, max_per_n: int | None = None) -> dict:
    ok = 0
    fails: list[dict] = []
    examples: list[dict] = []
    shortcut_used = 0
    for n in range(n_lo, n_hi + 1):
        base = nx.cycle_graph(n)
        non = [
            (u, v)
            for u in range(n)
            for v in range(u + 1, n)
            if not base.has_edge(u, v)
        ]
        count = 0
        for chords in combinations(non, 2):
            if len({*chords[0], *chords[1]}) < 4:
                continue
            g = base.copy()
            g.add_edges_from(chords)
            if max(d for _, d in g.degree()) > 3:
                continue
            if not chords_cross_on_cycle(n, chords[0], chords[1]):
                continue
            try:
                cert = derive_k4_via_path_fold(n, chords[0], chords[1])
                if not cert["residual_is_k4"] or not cert["derived_residual_xor_at_delta"]:
                    raise RuntimeError("bad residual")
            except Exception as exc:  # noqa: BLE001
                fails.append(
                    {
                        "n": n,
                        "chords": [list(c) for c in chords],
                        "error": str(exc),
                    }
                )
                continue
            ok += 1
            count += 1
            if "shortcut_fold" in cert.get("modes", []):
                shortcut_used += 1
            if len(examples) < 6:
                extra = certify_width_on_instance(
                    n, chords[0], chords[1], tuple(cert["residual_charges"])
                )
                examples.append({**{k: cert[k] for k in (
                    "n", "chords", "ends", "modes", "residual_charges",
                    "charges_match_contracted", "proof_steps", "residual_is_k4",
                )}, **extra})
            if max_per_n is not None and count >= max_per_n:
                break
    return {
        "ok": ok,
        "fails": fails,
        "shortcut_fold_instances": shortcut_used,
        "examples": examples,
        "note": (
            "Forward path-fold derives residual K4 XORs at width≤Δ for crossing "
            "instances (triangle ears + shortcut folds). Analytic projection "
            "lemma (refutation restriction) remains open for Lean/human."
        ),
    }


def main() -> int:
    report = verify_family(4, 10)
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(
        json.dumps(
            {
                "ok": report["ok"],
                "fails": len(report["fails"]),
                "shortcut_fold_instances": report["shortcut_fold_instances"],
                "first_fail": report["fails"][:1],
            },
            indent=2,
        )
    )
    print(f"wrote {OUT}")
    return 0 if report["ok"] > 0 and not report["fails"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
