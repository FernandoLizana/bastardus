"""Witness that both-stub triangle ears need target-sat (not pure XOR-sum)."""

from __future__ import annotations

import json
from pathlib import Path

import networkx as nx

from backend.proof_complexity.constructive_proofs import (
    _ProofBuilder,
    _all_axioms,
    _edge_var_map,
)
from backend.proof_complexity.xor_resolution import (
    clip_triangle_ear_xor,
    derive_xor_sum_on_pivot,
    xor_clauses,
)

OUT = Path("reports/discovery/xor_both_stubs_obstruction.json")


def _len2_setup(n: int = 6, a: int = 1) -> dict:
    """C_n + chord (a,a+2): tip a+1 with both Ou, Ow typically nonempty."""
    b = (a + 2) % n
    tip = (a + 1) % n
    g = nx.cycle_graph(n)
    g.add_edge(a, b)
    charges = {i: int(i == 0) for i in range(n)}
    e_index = _edge_var_map(g)
    delta = max(d for _, d in g.degree())
    x = e_index[tuple(sorted((a, tip)))]
    y = e_index[tuple(sorted((tip, b)))]
    z = e_index[tuple(sorted((a, b)))]
    ou = [
        e_index[tuple(sorted((a, nbr)))]
        for nbr in sorted(g.neighbors(a))
        if nbr not in (tip, b)
    ]
    ow = [
        e_index[tuple(sorted((b, nbr)))]
        for nbr in sorted(g.neighbors(b))
        if nbr not in (tip, a)
    ]
    return {
        "g": g,
        "charges": charges,
        "e_index": e_index,
        "delta": delta,
        "x": x,
        "y": y,
        "z": z,
        "ou": ou,
        "ow": ow,
        "chi_u": charges[a],
        "chi_v": charges[tip],
        "chi_w": charges[b],
        "n": n,
        "chord": [a, b],
        "tip": tip,
    }


def try_pure_xor_both_stubs() -> dict:
    s = _len2_setup()
    assert s["ou"] and s["ow"], "need both stub sides nonempty"
    chi_u, chi_v, chi_w = s["chi_u"], s["chi_v"], s["chi_w"]
    alpha = (chi_u + chi_v) % 2
    resid_u = xor_clauses([s["z"], *s["ou"]], alpha)
    resid_w = xor_clauses([s["z"], *s["ow"]], chi_w)

    builder = _ProofBuilder(_all_axioms(s["g"], s["charges"], s["e_index"]), delta=s["delta"])
    mid_err = glob_err = None
    try:
        derive_xor_sum_on_pivot(
            builder,
            [s["x"], s["z"], *s["ou"]],
            chi_u,
            [s["x"], s["y"]],
            chi_v,
            pivot=s["x"],
        )
    except RuntimeError as e:
        mid_err = str(e)
    if mid_err is None:
        try:
            derive_xor_sum_on_pivot(
                builder,
                [s["y"], s["z"], *s["ou"]],
                alpha,
                [s["y"], s["z"], *s["ow"]],
                chi_w,
                pivot=s["y"],
            )
        except RuntimeError as e:
            glob_err = str(e)
    pure_has_u = all(t in builder.index for t in resid_u)
    pure_has_w = all(t in builder.index for t in resid_w)

    builder2 = _ProofBuilder(_all_axioms(s["g"], s["charges"], s["e_index"]), delta=s["delta"])
    hybrid = clip_triangle_ear_xor(
        builder2,
        x=s["x"],
        y=s["y"],
        z=s["z"],
        ou=s["ou"],
        ow=s["ow"],
        chi_u=chi_u,
        chi_v=chi_v,
        chi_w=chi_w,
    )
    hybrid_has = all(t in builder2.index for t in resid_u + resid_w)
    pure_splits = pure_has_u and pure_has_w
    return {
        "config": {
            "n": s["n"],
            "chord": s["chord"],
            "tip": s["tip"],
            "ou": s["ou"],
            "ow": s["ow"],
            "charges_endpoints": [chi_u, chi_v, chi_w],
            "note": "both stub sides nonempty (cycle neighbors)",
        },
        "pure_xor_sums": {
            "mid_error": mid_err,
            "global_error": glob_err,
            "residual_u_present": pure_has_u,
            "residual_w_present": pure_has_w,
            "splits_residuals": pure_splits,
        },
        "hybrid_clip": {
            "mode": hybrid.get("mode"),
            "pure_xor_flag": hybrid.get("pure_xor"),
            "residuals_present": hybrid_has,
        },
        "obstruction": (
            "With both Ou, Ow nonempty, pivot XOR-sums alone do not place the "
            "separate endpoint residual CNFs; clip_triangle_ear_xor uses local "
            "XOR fill (then target-sat fallback)."
        ),
        "ok": (not pure_splits)
        and hybrid_has
        and hybrid.get("mode")
        in ("target_sat_residuals", "local_xor_residuals"),
    }


def main() -> int:
    report = try_pure_xor_both_stubs()
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(json.dumps(report, indent=2))
    print(f"wrote {OUT}")
    return 0 if report.get("ok") else 1


if __name__ == "__main__":
    raise SystemExit(main())
