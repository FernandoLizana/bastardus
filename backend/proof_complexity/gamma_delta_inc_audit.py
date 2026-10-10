"""Audit γ/Δ map `inc` samples: try higher width / report structure.

`inc` means no width-Δ refutation and no width-(Δ+1) (capped at 6) refutation
found by the oracle — often saturation incomplete or Width ≫ Δ.
"""

from __future__ import annotations

import json
from itertools import combinations
from pathlib import Path

import networkx as nx

from backend.proof_complexity.gamma_delta_width_map import classify, gamma
from backend.proof_complexity.tseitin_family import GraphInstance, tseitin_cnf
from backend.proof_complexity.width import has_width_refutation

OUT = Path("reports/discovery/gamma_delta_inc_audit.json")


def refine(g: nx.Graph, charges: tuple[int, ...], delta: int) -> dict:
    form = tseitin_cnf(GraphInstance(g, charges, "inc", 0, {}))
    results: dict[str, bool] = {}
    first_ok: int | None = None
    for w in range(delta, min(delta + 4, 8)):
        hit, _, _ = has_width_refutation(form, w)
        results[str(w)] = bool(hit)
        if hit and first_ok is None:
            first_ok = w
    base = classify(g, charges, delta)
    return {
        "gamma": gamma(g),
        "delta": delta,
        "base_label": base,
        "first_width_ok": first_ok,
        "by_width": results,
        "gap": None if first_ok is None else first_ok - delta,
    }


def collect_inc() -> list[dict]:
    samples: list[dict] = []
    # Same family as denser map — only keep `inc`
    for n in (5, 6, 7, 8):
        base = nx.cycle_graph(n)
        non = [
            (u, v)
            for u in range(n)
            for v in range(u + 1, n)
            if not base.has_edge(u, v)
        ]
        if n <= 6:
            kmax = 4
        elif n == 7:
            kmax = 3
        else:
            kmax = 2
        for k in range(0, kmax + 1):
            for ch in combinations(non, k):
                g = base.copy()
                g.add_edges_from(ch)
                if not nx.is_connected(g):
                    continue
                delta = max(d for _, d in g.degree())
                if delta > 4:
                    continue
                if n >= 7 and delta > 3:
                    continue
                charges = tuple(1 if i == 0 else 0 for i in range(n))
                lab = classify(g, charges, delta)
                if lab != "inc":
                    continue
                cert = refine(g, charges, delta)
                cert.update(
                    {
                        "n": n,
                        "chords": [list(c) for c in ch],
                        "m": g.number_of_edges(),
                    }
                )
                samples.append(cert)
                if len(samples) % 10 == 0:
                    print(f"inc collected {len(samples)}", flush=True)
    return samples


def main() -> int:
    samples = collect_inc()
    gaps = [s["gap"] for s in samples if s["gap"] is not None]
    still_inc = [s for s in samples if s["first_width_ok"] is None]
    by_gap: dict[str, int] = {}
    for g in gaps:
        by_gap[str(g)] = by_gap.get(str(g), 0) + 1
    report = {
        "total_inc": len(samples),
        "resolved_at_higher_w": len(gaps),
        "still_inc_up_to_delta_plus_3": len(still_inc),
        "by_gap": by_gap,
        "samples": samples[:60],
        "claim": (
            "`inc` at Δ means oracle found no Width≤Δ and no Width≤min(Δ+1,6) "
            "refutation. Reprobe up to Δ+3 (cap 7) to see how far Width sits."
        ),
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(
        f"wrote {OUT} inc={len(samples)} resolved={len(gaps)} "
        f"still={len(still_inc)} by_gap={by_gap}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
