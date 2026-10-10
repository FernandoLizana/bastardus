"""Path / vertex fold: eliminate deg-2 tip with optional shortcut edge.

When neighbors u,w of tip v are adjacent → triangle ear (absorb χ into one end).
When not adjacent → rebind surviving edge var as shortcut uw and absorb χ into fold_into.

Uses XOR-sum when possible; falls back to `_saturate_until_targets` for residual
XOR CNFs (no *global* empty-clause sat).
"""

from __future__ import annotations

from backend.proof_complexity.constructive_proofs import (
    Clause,
    _ProofBuilder,
    _saturate_until_targets,
    _xor_clauses_for_vertex,
)
from backend.proof_complexity.xor_resolution import derive_xor_sum_on_pivot


def incident_vars(
    g, e_index: dict[tuple[int, int], int], v: int, *, exclude: int | None = None
) -> list[int]:
    out: list[int] = []
    for n in sorted(g.neighbors(v)):
        if exclude is not None and n == exclude:
            continue
        out.append(e_index[tuple(sorted((v, n)))])
    return out


def fold_deg2_tip(
    builder: _ProofBuilder,
    work,
    charges: dict[int, int],
    e_index: dict[tuple[int, int], int],
    tip: int,
    *,
    fold_into: int | None = None,
) -> dict:
    """Eliminate one deg-2 tip; mutates work, charges, e_index."""
    if work.degree(tip) != 2:
        raise ValueError(f"tip {tip} has degree {work.degree(tip)}")
    u, w = list(work.neighbors(tip))
    if fold_into is None:
        fold_into = u
    if fold_into not in (u, w):
        raise ValueError("fold_into must be a neighbor of tip")
    other = w if fold_into == u else u

    x = e_index[tuple(sorted((fold_into, tip)))]
    y = e_index[tuple(sorted((tip, other)))]
    ou = incident_vars(work, e_index, fold_into, exclude=tip)
    chi_u = charges[fold_into] % 2
    chi_v = charges[tip] % 2
    chi_new = (chi_u + chi_v) % 2
    triangle = work.has_edge(fold_into, other)
    mode = "triangle_ear" if triangle else "shortcut_fold"

    if not triangle:
        # XOR-sum eq_fold ⊕ eq_tip on x → XOR({y}∪Ou)=χ_u⊕χ_v
        # (iterated local closure is inside derive_xor_sum_on_pivot)
        derive_xor_sum_on_pivot(
            builder, [x, *ou], chi_u, [x, y], chi_v, pivot=x
        )

    # Mutate residual graph
    work.remove_node(tip)
    del charges[tip]
    charges[fold_into] = chi_new
    e_index.pop(tuple(sorted((fold_into, tip))), None)
    e_index.pop(tuple(sorted((tip, other))), None)

    if triangle:
        # uw already present; y retired with tip–other
        pass
    else:
        # shortcut: keep y as (fold_into, other)
        work.add_edge(fold_into, other)
        e_index[tuple(sorted((fold_into, other)))] = y

    targets = _xor_clauses_for_vertex(
        work, e_index, fold_into, charges[fold_into]
    ) + _xor_clauses_for_vertex(work, e_index, other, charges[other])
    missing = [t for t in targets if t not in builder.index]
    if missing:
        _saturate_until_targets(builder, targets, width_cap=builder.delta)

    return {
        "tip": tip,
        "fold_into": fold_into,
        "other": other,
        "mode": mode,
        "triangle": triangle,
    }


def fold_open_arc_internals(
    builder: _ProofBuilder,
    work,
    charges: dict[int, int],
    e_index: dict[tuple[int, int], int],
    left: int,
    internals: list[int],
    right: int,
) -> list[dict]:
    """Fold path left–internals–right from the left, absorbing into the growing left."""
    log: list[dict] = []
    # Walk current path from left toward right
    while internals:
        # Find tip adjacent to current left on the residual path
        tip = None
        for v in internals:
            if work.has_edge(left, v) and work.degree(v) == 2:
                tip = v
                break
        if tip is None:
            # maybe next internal already adjacent via prior folds
            nbrs = [n for n in work.neighbors(left) if n in internals]
            if not nbrs:
                raise RuntimeError(
                    f"cannot locate next tip on arc left={left} internals={internals}"
                )
            tip = nbrs[0]
        rec = fold_deg2_tip(
            builder, work, charges, e_index, tip, fold_into=left
        )
        log.append(rec)
        internals = [v for v in internals if v != tip]
    # After folds, left should be adjacent to right
    if not work.has_edge(left, right):
        raise RuntimeError(f"after arc fold missing edge {left}-{right}")
    return log
