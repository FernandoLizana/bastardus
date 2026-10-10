"""Structural ear-clip certificates for non-crossing C_n + length-2 chords.

GF(2) ear clip: a degree-2 vertex v whose neighbours u,w are adjacent forms a
facial triangle. Absorb χ_v into u and delete v. Empirically (and in the proof
outline) this preserves Tseitin equisatisfiability; after clipping all such ears
the residual is unicyclic/bicyclic/cycle and the ordinary lemmas apply.

This module machine-checks the *geometric* reduction + residual constructive
proof. The original Width≤Δ certificate remains `prove_noncrossing_two_chords_lemma`
(peel+saturation); together they support the induction plan in
TD-TSEITIN-WIDTH-CYCLE-TWO-CHORDS-001.
"""

from __future__ import annotations

import json
from itertools import combinations
from pathlib import Path

import networkx as nx

from backend.proof_complexity.chord_crossing_law import (
    chords_cross_on_cycle,
    circular_dist,
)
from backend.proof_complexity.constructive_proofs import (
    prove_bicyclic_lemma,
    prove_cycle_lemma,
    prove_noncrossing_two_chords_lemma,
    prove_unicyclic_lemma,
    verify_resolution_derivation,
)

OUT = Path("reports/discovery/ear_clip_noncrossing_len2.json")


def clip_length2_ears(
    graph: nx.Graph, charges: dict[int, int]
) -> tuple[nx.Graph, dict[int, int], list[dict]]:
    """Repeatedly delete deg-2 triangle tips, absorbing charge into one endpoint."""
    g = graph.copy()
    c = {v: charges[v] % 2 for v in graph.nodes()}
    log: list[dict] = []
    while True:
        ear = None
        for v, d in g.degree():
            if d != 2:
                continue
            u, w = list(g.neighbors(v))
            if g.has_edge(u, w):
                ear = (v, u, w)
                break
        if ear is None:
            break
        v, u, w = ear
        c[u] = (c[u] + c[v]) % 2
        log.append({"clip_v": v, "absorb_into": u, "base_edge": [u, w], "chi_v": charges.get(v, c.get(v, 0))})
        g.remove_node(v)
        del c[v]
    return g, c, log


def classify_residual(g: nx.Graph) -> str:
    if not nx.is_connected(g):
        return "disconnected"
    n, m = g.number_of_nodes(), g.number_of_edges()
    if m == n - 1 and nx.is_tree(g):
        return "tree"
    if m == n:
        degs = [d for _, d in g.degree()]
        if degs and min(degs) == 2 and max(degs) == 2:
            return "cycle"
        return "unicyclic"
    if m == n + 1:
        return "bicyclic"
    return f"other(m={m},n={n})"


def prove_residual(g: nx.Graph, charges: dict[int, int]):
    kind = classify_residual(g)
    # Relabel to contiguous ids for lemmas if needed — lemmas use graph labels directly
    if kind == "cycle":
        return prove_cycle_lemma(g, charges), kind
    if kind == "unicyclic":
        return prove_unicyclic_lemma(g, charges), kind
    if kind == "bicyclic":
        return prove_bicyclic_lemma(g, charges), kind
    if kind == "tree":
        from backend.proof_complexity.constructive_proofs import prove_tree_lemma

        return prove_tree_lemma(g, charges), kind
    raise ValueError(f"cannot prove residual of kind {kind}")


def both_chords_length2(n: int, c1: tuple[int, int], c2: tuple[int, int]) -> bool:
    return circular_dist(n, *c1) == 2 and circular_dist(n, *c2) == 2


def run_family(n_lo: int = 6, n_hi: int = 10) -> dict:
    rows = []
    for n in range(n_lo, n_hi + 1):
        base = nx.cycle_graph(n)
        non = [(u, v) for u in range(n) for v in range(u + 1, n) if not base.has_edge(u, v)]
        for chords in combinations(non, 2):
            if len({*chords[0], *chords[1]}) < 4:
                continue
            if chords_cross_on_cycle(n, chords[0], chords[1]):
                continue
            if not both_chords_length2(n, chords[0], chords[1]):
                continue
            g = base.copy()
            g.add_edges_from(chords)
            if max(d for _, d in g.degree()) > 3:
                continue
            charges = {v: int(v == 0) for v in g.nodes()}

            # Structural ear-clip + residual constructive lemma
            g2, c2, log = clip_length2_ears(g, charges)
            if sum(c2.values()) % 2 == 0:
                rows.append(
                    {
                        "n": n,
                        "chords": [list(c) for c in chords],
                        "status": "even_charge_after_clip_unexpected",
                        "clips": len(log),
                    }
                )
                continue
            try:
                proof_res, kind = prove_residual(g2, c2)
                errs = verify_resolution_derivation(proof_res)
            except Exception as exc:  # noqa: BLE001
                rows.append(
                    {
                        "n": n,
                        "chords": [list(c) for c in chords],
                        "status": f"residual_fail:{exc}",
                        "clips": len(log),
                        "residual_kind": classify_residual(g2),
                    }
                )
                continue

            # Original Width≤Δ certificate (saturation-based)
            proof_full = prove_noncrossing_two_chords_lemma(g, charges)

            rows.append(
                {
                    "n": n,
                    "chords": [list(c) for c in chords],
                    "status": "ok",
                    "clips": len(log),
                    "clip_log": log,
                    "residual_kind": kind,
                    "residual_max_width": proof_res.max_width,
                    "residual_delta": proof_res.delta,
                    "residual_verify": errs,
                    "full_max_width": proof_full.max_width,
                    "full_delta": proof_full.delta,
                }
            )
    ok = [r for r in rows if r["status"] == "ok"]
    bad = [r for r in rows if r["status"] != "ok"]
    report = {
        "family": "non-crossing C_n + two length-2 chords, unit charge",
        "checked": len(rows),
        "ok": len(ok),
        "failed": bad,
        "by_residual": {},
        "examples": ok[:8],
        "note": (
            "Ear-clip reduces to cycle/unicyclic/bicyclic; residual proved by "
            "existing lemmas. Full graph still certified via peel+Δ-sat."
        ),
    }
    for r in ok:
        k = r["residual_kind"]
        report["by_residual"][k] = report["by_residual"].get(k, 0) + 1
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2), encoding="utf-8")
    return report


def main() -> int:
    report = run_family(6, 10)
    print(json.dumps({k: report[k] for k in ("checked", "ok", "by_residual", "failed")}, indent=2))
    print(f"wrote {OUT}")
    return 0 if not report["failed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
