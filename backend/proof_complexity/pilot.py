"""Pilot discovery campaign: Tseitin width vs graph structure (Stage A).

Promotion policy: outputs are R0–R2 only unless a manual proof is attached.
"""

from __future__ import annotations

import json
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable

from backend.proof_complexity.tseitin_family import (
    GraphInstance,
    graph_metrics,
    make_cycle,
    make_grid,
    make_path,
    make_random_regular,
    make_tree_random,
    make_two_cycles_bridge,
    tseitin_cnf,
)
from backend.proof_complexity.width import min_resolution_width


@dataclass
class PilotRow:
    family: str
    seed: int
    n: int
    max_degree: int
    is_tree: bool
    is_cycle: bool
    tw_upper: int | None
    edge_connectivity: int
    width: int
    axiom_width: int
    closure_notes: list[str]


def _enumerate_instances() -> list[GraphInstance]:
    """Stage A budget: small, max-degree ≤ 3 graphs only."""
    insts: list[GraphInstance] = []
    for n in range(3, 9):
        insts.append(make_path(n))
        insts.append(make_cycle(n))
        for seed in range(8):
            insts.append(make_tree_random(n, seed=seed))
    for a, b in [(2, 2), (2, 3), (3, 3)]:
        insts.append(make_grid(a, b))
    for a, b in [(3, 3), (4, 4), (5, 3), (6, 4)]:
        insts.append(make_two_cycles_bridge(a, b))
    for n, seed in [(6, 0), (6, 1), (8, 0), (8, 1), (8, 2)]:
        try:
            insts.append(make_random_regular(n, 3, seed=seed))
        except Exception:  # noqa: BLE001
            pass
    # Explicit high-degree trees to stress Δ
    # (star is a tree)
    return insts


def run_pilot(output_dir: str | Path = "reports/discovery") -> dict[str, Any]:
    out = Path(output_dir)
    out.mkdir(parents=True, exist_ok=True)
    rows: list[dict[str, Any]] = []
    for inst in _enumerate_instances():
        formula = tseitin_cnf(inst)
        metrics = graph_metrics(inst.graph)
        if not metrics.get("connected"):
            continue
        if sum(inst.charges) % 2 == 0:
            continue
        # Skip high degree (XOR CNF explodes)
        if metrics["max_degree"] > 3:
            continue
        cert = min_resolution_width(formula, max_width=max(metrics["max_degree"] + 3, 5))
        if cert.claimed_min_width < 0:
            continue
        if cert.claim_type == "error_or_inconclusive":
            continue
        row = {
            "family": inst.family,
            "seed": inst.seed,
            "n": metrics["n"],
            "m": metrics["m"],
            "max_degree": metrics["max_degree"],
            "is_tree": metrics["is_tree"],
            "is_cycle": metrics["is_cycle"],
            "tw_upper": metrics["treewidth_min_fill_upper"],
            "edge_connectivity": metrics["edge_connectivity"],
            "width": cert.claimed_min_width,
            "axiom_lower": metrics["max_degree"],
            "notes": cert.notes,
            "formula_hash": formula.content_hash(),
            "evidence_level": "E2",
            "promotion_rank": "R0_raw",
        }
        rows.append(row)

    # Refute candidate conjectures
    conjectures = _default_conjectures()
    refutation_reports = []
    for conj in conjectures:
        report = _try_refute(conj, rows)
        refutation_reports.append(report)

    survivors = [r for r in refutation_reports if not r["refuted"]]
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    payload = {
        "timestamp": stamp,
        "n_instances": len(rows),
        "rows": rows,
        "refutations": refutation_reports,
        "survivors": survivors,
        "disclaimer": (
            "Pilot A only. Survival ≠ truth. tw_upper is heuristic. "
            "No P vs NP claim."
        ),
    }
    path = out / f"pilot_tseitin_width_{stamp}.json"
    path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    (out / "pilot_tseitin_width_latest.json").write_text(
        json.dumps(payload, indent=2), encoding="utf-8"
    )
    return payload


def _default_conjectures() -> list[dict[str, Any]]:
    return [
        {
            "id": "C1_width_ge_tw_upper",
            "statement": "For all tested unsat Tseitin instances, Width ≥ tw_upper(heuristic).",
            "predicate": lambda r: r["tw_upper"] is None or r["width"] >= r["tw_upper"],
            "status": "R2_candidate",
            "literature_status": "Likely false; tw_upper is an upper bound on tw, Width can be < tw.",
        },
        {
            "id": "C2_width_eq_max_degree_always",
            "statement": "Width(T(G,c)) = Δ(G) for all connected G with odd charge.",
            "predicate": lambda r: r["width"] == r["max_degree"],
            "status": "R2_candidate",
            "literature_status": "False in general (expanders need large width ≫ Δ).",
        },
        {
            "id": "C3_width_eq_delta_on_trees",
            "statement": "If G is a tree and charge sum odd, Width(T(G,c)) = Δ(G).",
            "predicate": lambda r: (not r["is_tree"]) or r["width"] == r["max_degree"],
            "status": "R2_candidate",
            "literature_status": "Plausible; trees have tw=1; axioms force Δ.",
        },
        {
            "id": "C4_width_eq_2_on_cycles",
            "statement": "If G is a cycle and charge sum odd, Width(T(G,c)) = 2.",
            "predicate": lambda r: (not r["is_cycle"]) or r["width"] == 2,
            "status": "R2_candidate",
            "literature_status": "Plausible; Δ=2 and parity propagation.",
        },
        {
            "id": "C5_width_ge_edge_connectivity",
            "statement": "Width ≥ edge_connectivity(G) for odd-charge connected Tseitin.",
            "predicate": lambda r: r["width"] >= r["edge_connectivity"],
            "status": "R2_candidate",
            "literature_status": "Unclear; to be stress-tested.",
        },
    ]


def _try_refute(conj: dict[str, Any], rows: list[dict[str, Any]]) -> dict[str, Any]:
    pred: Callable[[dict[str, Any]], bool] = conj["predicate"]
    counter = None
    for r in sorted(rows, key=lambda x: (x["n"], x["m"], x["family"])):
        if not pred(r):
            counter = r
            break
    return {
        "id": conj["id"],
        "statement": conj["statement"],
        "literature_status": conj["literature_status"],
        "refuted": counter is not None,
        "minimal_counterexample": counter,
        "promotion": "refuted_R2" if counter is not None else "survives_pilot_R3_local",
        "caveat": (
            "Pilot A sample only — survival is not R3 global. "
            "tw_upper heuristic contaminates C1."
        ),
    }


if __name__ == "__main__":
    result = run_pilot()
    print(json.dumps({"n": result["n_instances"], "survivors": result["survivors"]}, indent=2))
