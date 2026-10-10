"""Mass-test XOR ear-clip modes on length-2 chord ears (Category C)."""

from __future__ import annotations

import json
from collections import Counter
from pathlib import Path

import networkx as nx

from backend.proof_complexity.constructive_proofs import (
    _ProofBuilder,
    _all_axioms,
    _edge_var_map,
    prove_bicyclic_pathfold_lemma,
    prove_outerplanar_pathfold_lemma,
)
from backend.proof_complexity.xor_resolution import clip_triangle_ear_xor, demo_triangle_ear_xor

OUT = Path("reports/discovery/xor_ear_modes.json")


def clip_len2_ear(n: int, a: int) -> dict:
    """C_n + chord (a,a+2): tip a+1."""
    b = (a + 2) % n
    tip = (a + 1) % n
    g = nx.cycle_graph(n)
    g.add_edge(a, b)
    charges = {i: int(i == 0) for i in range(n)}
    e_index = _edge_var_map(g)
    delta = max(d for _, d in g.degree())
    builder = _ProofBuilder(_all_axioms(g, charges, e_index), delta=delta)
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
    out = clip_triangle_ear_xor(
        builder,
        x=x,
        y=y,
        z=z,
        ou=ou,
        ow=ow,
        chi_u=charges[a],
        chi_v=charges[tip],
        chi_w=charges[b],
    )
    return {
        "n": n,
        "chord": [a, b],
        "tip": tip,
        "ou_len": len(ou),
        "ow_len": len(ow),
        "mode": out.get("mode"),
        "pure_xor": out.get("pure_xor", False),
        "empty": () in builder.index,
        "steps": len(builder.steps),
    }


def main() -> int:
    demo = demo_triangle_ear_xor()
    modes: Counter[str] = Counter()
    samples: list[dict] = []
    ok = fail = 0
    for n in range(4, 10):
        for a in range(n):
            try:
                rec = clip_len2_ear(n, a)
                modes[str(rec["mode"])] += 1
                ok += 1
                if len(samples) < 10:
                    samples.append(rec)
            except Exception as e:  # noqa: BLE001
                fail += 1
                if len(samples) < 10:
                    samples.append({"n": n, "a": a, "error": str(e)})

    g = nx.cycle_graph(6)
    g.add_edge(0, 2)
    prove_bicyclic_pathfold_lemma(g, {i: int(i == 0) for i in range(6)})
    g2 = nx.cycle_graph(7)
    g2.add_edges_from([(0, 2), (3, 5)])
    prove_outerplanar_pathfold_lemma(g2, {i: int(i == 0) for i in range(7)})

    report = {
        "demo_triangle": demo,
        "len2_ear_clips": {"ok": ok, "fail": fail, "modes": dict(modes)},
        "samples": samples,
        "note": "Each directed length-2 ear (a,a+2) clipped once at tip a+1.",
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(json.dumps({"demo": demo, "modes": dict(modes), "ok": ok, "fail": fail}, indent=2))
    print(f"wrote {OUT}")
    return 0 if fail == 0 and demo.get("ok") else 1


if __name__ == "__main__":
    raise SystemExit(main())
