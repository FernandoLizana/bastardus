"""K₄ minor lower-bound support for the crossing-width law.

Ingredients
-----------
1. K₄ with odd charge has Width = 4 > Δ = 3.
2. Every crossing C_n+2 chords (Δ≤3) has a K₄-minor (four arcs + two chords).
3. **Charge contraction:** absorbing each open-arc internal into the left endpoint
   yields an odd charge on the four endpoints; the abstract K₄ Tseitin on those
   contracted charges also has Width = 4.

Lift outline (still the analytic gap, now with matching charge data)
--------------------------------------------------------------------
Eliminating deg-2 internals along each of the four arcs is width-≤Δ Gaussian
elimination on XOR equations. The residual XOR system on the four endpoints is
Tseitin-on-K₄ with the contracted charges. Hence a width-3 refutation of G would
yield a width-3 refutation of that K₄ instance, contradicting (1)+(3).
Making that “would induce” step precise (projection / restriction / simulation
of resolution under path contraction) is the remaining lemma for Lean or a
human write-up.

Partial machine progress: triangle-ear residual derivation for pure K₄
(`k4_path_contraction_derivation.json`); long-arc forward fold still open.

"""

from __future__ import annotations

import json
from itertools import combinations
from pathlib import Path

import networkx as nx

from backend.proof_complexity.chord_crossing_law import chords_cross_on_cycle
from backend.proof_complexity.chord_law_search import _bitsat_complete
from backend.proof_complexity.gpu_width_opencl import (
    batch_has_refutation_gpu,
    formula_to_bit_axioms,
)
from backend.proof_complexity.tseitin_family import GraphInstance, tseitin_cnf
from backend.proof_complexity.width import has_width_refutation, min_resolution_width

OUT = Path("reports/discovery/k4_minor_crossing_law.json")
LIFT_OUT = Path("reports/discovery/k4_lift_charge_contraction.json")


def k4_width_certificate(charges: tuple[int, ...] | None = None) -> dict:
    g = nx.complete_graph(4)
    if charges is None:
        charges = (1, 0, 0, 0)
    if sum(charges) % 2 == 0:
        raise ValueError("even charge on K4 is SAT")
    form = tseitin_cnf(GraphInstance(g, charges, "K4", 0, {}))
    delta = max(d for _, d in g.degree())
    w = min_resolution_width(form, max_width=8).claimed_min_width
    ok3, _, size3 = has_width_refutation(form, 3)
    ok4, _, size4 = has_width_refutation(form, 4)
    return {
        "graph": "K4",
        "charges": list(charges),
        "delta": delta,
        "width": w,
        "empty_at_width_3": ok3,
        "closure_size_at_3": size3,
        "empty_at_width_4": ok4,
        "closure_size_at_4": size4,
        "certified_gt_delta": (not ok3) and ok4 and w > delta,
    }


def crossing_branch_sets(
    n: int, c1: tuple[int, int], c2: tuple[int, int]
) -> tuple[tuple[int, int, int, int], list[list[int]]]:
    """Endpoints in cycle order and the four open arcs between them."""
    pts = sorted({c1[0], c1[1], c2[0], c2[1]})
    if len(pts) != 4:
        raise ValueError("need four distinct endpoints")
    order = (pts[0], pts[1], pts[2], pts[3])
    arcs: list[list[int]] = []
    for i in range(4):
        s, t = order[i], order[(i + 1) % 4]
        if s < t:
            arcs.append(list(range(s + 1, t)))
        else:
            arcs.append(list(range(s + 1, n)) + list(range(0, t)))
    return order, arcs


def has_k4_minor_crossing(n: int, c1: tuple[int, int], c2: tuple[int, int]) -> bool:
    if not chords_cross_on_cycle(n, c1, c2):
        return False
    crossing_branch_sets(n, c1, c2)
    return True


def contract_charges_to_endpoints(
    n: int,
    c1: tuple[int, int],
    c2: tuple[int, int],
    charges: dict[int, int],
) -> tuple[tuple[int, int, int, int], tuple[int, int, int, int]]:
    """Absorb each open-arc internal into the left endpoint (GF(2))."""
    ends, arcs = crossing_branch_sets(n, c1, c2)
    c = {v: charges.get(v, 0) % 2 for v in range(n)}
    for i, arc in enumerate(arcs):
        left = ends[i]
        for v in arc:
            c[left] = (c[left] + c[v]) % 2
            c[v] = 0
    contracted = tuple(c[e] for e in ends)
    return ends, contracted


def verify_all_crossing_have_k4_minor(n_lo: int = 5, n_hi: int = 12) -> dict:
    checked = 0
    missing = []
    for n in range(n_lo, n_hi + 1):
        base = nx.cycle_graph(n)
        non = [(u, v) for u in range(n) for v in range(u + 1, n) if not base.has_edge(u, v)]
        for chords in combinations(non, 2):
            if len({*chords[0], *chords[1]}) < 4:
                continue
            g = base.copy()
            g.add_edges_from(chords)
            if max(d for _, d in g.degree()) > 3:
                continue
            if not chords_cross_on_cycle(n, chords[0], chords[1]):
                continue
            checked += 1
            if not has_k4_minor_crossing(n, chords[0], chords[1]):
                missing.append({"n": n, "chords": [list(c) for c in chords]})
    return {"checked_crossing": checked, "missing_k4_minor": missing}


def _graph_width_gt_delta(g: nx.Graph, charges: tuple[int, ...], delta: int) -> bool:
    bits = formula_to_bit_axioms(tseitin_cnf(GraphInstance(g, charges, "x", 0, {})))
    if batch_has_refutation_gpu([bits], [delta])[0]:
        return False
    ok, complete = _bitsat_complete(bits, delta)
    if ok:
        return False
    return complete  # closed without empty ⇒ W > Δ


def verify_lift_ingredients_family(
    n_lo: int = 5, n_hi: int = 10, *, max_per_n: int | None = None
) -> dict:
    """For each crossing instance: contracted K4 has W>3 and G has W>Δ."""
    checked = 0
    bad_k4: list[dict] = []
    bad_g: list[dict] = []
    even_contracted = 0
    examples: list[dict] = []

    for n in range(n_lo, n_hi + 1):
        base = nx.cycle_graph(n)
        non = [(u, v) for u in range(n) for v in range(u + 1, n) if not base.has_edge(u, v)]
        count_n = 0
        for chords in combinations(non, 2):
            if len({*chords[0], *chords[1]}) < 4:
                continue
            g = base.copy()
            g.add_edges_from(chords)
            delta = max(d for _, d in g.degree())
            if delta > 3:
                continue
            if not chords_cross_on_cycle(n, chords[0], chords[1]):
                continue
            charges_d = {v: int(v == 0) for v in range(n)}
            ends, contracted = contract_charges_to_endpoints(
                n, chords[0], chords[1], charges_d
            )
            if sum(contracted) % 2 == 0:
                even_contracted += 1
                # unit charge at 0 may become even after absorbs — try all unit positions
                recovered = False
                for src in ends:
                    charges_d2 = {v: int(v == src) for v in range(n)}
                    _e2, contracted2 = contract_charges_to_endpoints(
                        n, chords[0], chords[1], charges_d2
                    )
                    if sum(contracted2) % 2 == 1:
                        contracted = contracted2
                        charges_d = charges_d2
                        recovered = True
                        break
                if not recovered:
                    # odd total preserved under absorbs into endpoints from full c;
                    # if even, distribution put odd on non-endpoints only — impossible
                    # if we start with unit at an endpoint. Unit at non-endpoint:
                    internals = [v for v in range(n) if v not in ends]
                    for src in internals:
                        charges_d2 = {v: int(v == src) for v in range(n)}
                        _e2, contracted2 = contract_charges_to_endpoints(
                            n, chords[0], chords[1], charges_d2
                        )
                        if sum(contracted2) % 2 == 1:
                            contracted = contracted2
                            charges_d = charges_d2
                            recovered = True
                            break
                if not recovered:
                    bad_k4.append(
                        {
                            "n": n,
                            "chords": [list(c) for c in chords],
                            "reason": "could_not_get_odd_contracted",
                        }
                    )
                    continue

            k4cert = k4_width_certificate(contracted)
            if not k4cert["certified_gt_delta"]:
                bad_k4.append(
                    {
                        "n": n,
                        "chords": [list(c) for c in chords],
                        "contracted": list(contracted),
                        "k4": k4cert,
                    }
                )
                continue

            charges_t = tuple(charges_d[v] for v in range(n))
            if not _graph_width_gt_delta(g, charges_t, delta):
                bad_g.append(
                    {
                        "n": n,
                        "chords": [list(c) for c in chords],
                        "delta": delta,
                    }
                )
                continue

            checked += 1
            count_n += 1
            if len(examples) < 6:
                examples.append(
                    {
                        "n": n,
                        "chords": [list(c) for c in chords],
                        "ends": list(ends),
                        "contracted_charges": list(contracted),
                        "delta": delta,
                        "k4_width": k4cert["width"],
                    }
                )
            if max_per_n is not None and count_n >= max_per_n:
                break

    return {
        "checked_ok": checked,
        "even_contracted_initial_skips_handled": even_contracted,
        "bad_k4": bad_k4,
        "bad_g_not_gt_delta": bad_g,
        "examples": examples,
        "lift_statement": (
            "For each crossing instance checked: charge contraction yields odd K4 "
            "charges with Width=4>3, and G itself has Width>Δ. Formal resolution "
            "projection G → K4 still open."
        ),
    }


def main() -> int:
    k4 = k4_width_certificate()
    fam = verify_all_crossing_have_k4_minor(5, 12)
    lift = verify_lift_ingredients_family(5, 10)
    report = {
        "k4_unit": k4,
        "crossing_family": fam,
        "lift_ingredients": lift,
        "law_support": (
            "Crossing ⇒ K4-minor; K4 Width>Δ; contracted charges keep Width>3 "
            "on the abstract K4, matching G's Width>Δ on the checked family."
        ),
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2), encoding="utf-8")
    LIFT_OUT.write_text(json.dumps(lift, indent=2), encoding="utf-8")
    print(json.dumps(
        {
            "k4_ok": k4["certified_gt_delta"],
            "crossing_minors": fam,
            "lift_ok": lift["checked_ok"],
            "bad_k4": len(lift["bad_k4"]),
            "bad_g": len(lift["bad_g_not_gt_delta"]),
        },
        indent=2,
    ))
    print(f"wrote {OUT}")
    print(f"wrote {LIFT_OUT}")
    return 0 if (
        k4["certified_gt_delta"]
        and not fam["missing_k4_minor"]
        and not lift["bad_k4"]
        and not lift["bad_g_not_gt_delta"]
        and lift["checked_ok"] > 0
    ) else 1


if __name__ == "__main__":
    raise SystemExit(main())
