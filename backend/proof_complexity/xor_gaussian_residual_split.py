"""CNF-level XOR Gaussian step: iterated pivot-sums toward residual CNFs.

Does not replace local/target sat for both-stub ears in general graphs, but
records when iterated XOR-sum + local fill on allowed vars recovers residuals.
"""

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
    derive_xor_sum_on_pivot,
    fill_xor_by_local_sat,
    xor_clauses,
)

OUT = Path("reports/discovery/xor_gaussian_residual_split.json")


def _len2_both_stubs(n: int = 6, a: int = 1) -> dict:
    b = (a + 2) % n
    tip = (a + 1) % n
    g = nx.cycle_graph(n)
    g.add_edge(a, b)
    charges = {i: int(i == 0) for i in range(n)}
    e = _edge_var_map(g)
    delta = max(d for _, d in g.degree())
    x = e[tuple(sorted((a, tip)))]
    y = e[tuple(sorted((tip, b)))]
    z = e[tuple(sorted((a, b)))]
    ou = [
        e[tuple(sorted((a, nbr)))]
        for nbr in sorted(g.neighbors(a))
        if nbr not in (tip, b)
    ]
    ow = [
        e[tuple(sorted((b, nbr)))]
        for nbr in sorted(g.neighbors(b))
        if nbr not in (tip, a)
    ]
    return {
        "g": g,
        "charges": charges,
        "e": e,
        "delta": delta,
        "x": x,
        "y": y,
        "z": z,
        "ou": ou,
        "ow": ow,
        "chi_u": charges[a],
        "chi_v": charges[tip],
        "chi_w": charges[b],
    }


def attempt_gaussian_split(s: dict) -> dict:
    """Iterated XOR-sum on tip then local fills on residual supports only."""
    builder = _ProofBuilder(
        _all_axioms(s["g"], s["charges"], s["e"]), delta=s["delta"]
    )
    chi_u, chi_v, chi_w = s["chi_u"], s["chi_v"], s["chi_w"]
    alpha = (chi_u + chi_v) % 2
    log: list[str] = []
    # mid = eq_u ⊕ eq_v on x
    try:
        derive_xor_sum_on_pivot(
            builder,
            [s["x"], s["z"], *s["ou"]],
            chi_u,
            [s["x"], s["y"]],
            chi_v,
            pivot=s["x"],
        )
        log.append("mid_xor_sum_ok")
    except RuntimeError as e:
        try:
            fill_xor_by_local_sat(
                builder,
                [s["y"], s["z"], *s["ou"]],
                alpha,
                width_cap=s["delta"],
            )
            log.append(f"mid_local_fill_ok after {e}")
        except RuntimeError as e2:
            return {
                "ok": False,
                "log": log + [f"mid_fail {e2}"],
                "mode": "fail_mid",
            }

    resid_u = xor_clauses([s["z"], *s["ou"]], alpha)
    resid_w = xor_clauses([s["z"], *s["ow"]], chi_w)

    # Try residual fills using only residual vars (true local Gaussian)
    u_ok = w_ok = False
    try:
        fill_xor_by_local_sat(
            builder, [s["z"], *s["ou"]], alpha, width_cap=s["delta"]
        )
        u_ok = all(t in builder.index for t in resid_u)
        log.append("resid_u_local_ok" if u_ok else "resid_u_local_incomplete")
    except RuntimeError as e:
        log.append(f"resid_u_local_fail {e}")

    try:
        fill_xor_by_local_sat(
            builder, [s["z"], *s["ow"]], chi_w, width_cap=s["delta"]
        )
        w_ok = all(t in builder.index for t in resid_w)
        log.append("resid_w_local_ok" if w_ok else "resid_w_local_incomplete")
    except RuntimeError as e:
        log.append(f"resid_w_local_fail {e}")

    pure = u_ok and w_ok
    return {
        "ok": True,
        "splits_without_global_sat": pure,
        "resid_u": u_ok,
        "resid_w": w_ok,
        "log": log,
        "mode": "local_gaussian" if pure else "local_incomplete",
        "note": (
            "Local-only fill after tip XOR-sum; fails when joint cancel needs "
            "bridge vars (matches XOR_EAR obstruction)."
        ),
    }


def main() -> int:
    s = _len2_both_stubs()
    assert s["ou"] and s["ow"]
    report = {
        "config": {
            "ou": s["ou"],
            "ow": s["ow"],
            "delta": s["delta"],
        },
        "gaussian_attempt": attempt_gaussian_split(s),
    }
    # Expectation: not a full split (documents remaining gap)
    report["gap_remains"] = not report["gaussian_attempt"].get(
        "splits_without_global_sat", False
    )
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(json.dumps(report, indent=2))
    print(f"wrote {OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
