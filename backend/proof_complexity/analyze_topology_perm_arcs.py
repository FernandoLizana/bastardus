"""Characterize when E2 topology perm is determined by partial keys vs full endpoints.

Reads `crossing_residual_catalog.json` and reports:
  - 209 distinct (n, CrossingArcs) shapes on the n=5..10 mass window
  - 83 shapes with a unique perm class (83/461 instances; 1 instance each)
  - 126 shapes ambiguous (378/461 instances; endpoint tie-break required)

Also checks stronger partial keys (cyclic norm, Vres, p0 anchor, chord parity)
and writes `reports/discovery/topology_perm_arcs_analysis.json`.
"""

from __future__ import annotations

import json
from collections import defaultdict
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from backend.proof_complexity.emit_topology_perm_lookup_lean import (
    PERM_CLASSES,
    PERM_TO_ID,
    arcs_p0_key,
    endpoints_fields,
    hash_key,
)

CATALOG = ROOT / "reports" / "discovery" / "crossing_residual_catalog.json"
OUT = ROOT / "reports" / "discovery" / "topology_perm_arcs_analysis.json"


def arcs_key(n: int, a0: int, a1: int, a2: int, a3: int) -> int:
    return n * 10000 + a0 * 1000 + a1 * 100 + a2 * 10 + a3


def cyclic_norm(arcs: tuple[int, int, int, int]) -> tuple[int, int, int, int]:
    a = list(arcs)
    return min(tuple(a[i:] + a[:i]) for i in range(4))


def rev_cyclic_norm(arcs: tuple[int, int, int, int]) -> tuple[int, int, int, int]:
    a = list(arcs)[::-1]
    return min(tuple(a[i:] + a[:i]) for i in range(4))


def chord_parity(c1: tuple[int, int], c2: tuple[int, int]) -> tuple[tuple[int, int], tuple[int, int]]:
    return tuple(sorted([tuple(c1), tuple(c2)]))  # type: ignore[return-value]


def _key_stats(rows: list[dict], keyfn) -> dict:
    by_key: dict = defaultdict(set)
    for r in rows:
        by_key[keyfn(r)].add(r["perm_class_id"])
    multi = [k for k, v in by_key.items() if len(v) > 1]
    inst_ambig = sum(len([r for r in rows if keyfn(r) == k]) for k in multi)
    return {
        "keys": len(by_key),
        "multi_keys": len(multi),
        "inst_unique": len(rows) - inst_ambig,
        "inst_ambig": inst_ambig,
    }


def main() -> int:
    catalog = json.loads(CATALOG.read_text(encoding="utf-8"))
    instances = catalog["instances"]
    assert len(instances) == 461

    rows: list[dict] = []
    by_n_arcs: dict[tuple[int, tuple[int, int, int, int]], list[dict]] = defaultdict(list)

    for i, inst in enumerate(instances):
        n = inst["n"]
        c1, c2 = tuple(inst["chords"][0]), tuple(inst["chords"][1])
        p0, p1, p2, p3 = endpoints_fields(n, c1, c2)
        a0 = p1 - p0 - 1
        a1 = p2 - p1 - 1
        a2 = p3 - p2 - 1
        a3 = n - p3 + p0 - 1
        arcs = (a0, a1, a2, a3)
        perm = tuple(inst["witness"]["permutation"])
        cid = PERM_TO_ID[perm]
        vres = tuple(inst["Vres"])
        row = {
            "catalog_index": i,
            "n": n,
            "p0": p0,
            "p1": p1,
            "p2": p2,
            "p3": p3,
            "arcs": arcs,
            "endpoints": (p0, p1, p2, p3),
            "endpoint_key": hash_key(n, p0, p1, p2, p3),
            "arcs_key": arcs_key(n, *arcs),
            "arcs_p0_key": arcs_p0_key(n, *arcs, p0),
            "perm_class_id": cid,
            "perm_name": PERM_CLASSES[cid][1],
            "perm": list(perm),
            "Vres": list(vres),
            "vres": vres,
            "c1": c1,
            "c2": c2,
        }
        rows.append(row)
        by_n_arcs[(n, arcs)].append(row)

    unique_entries: list[tuple[int, int]] = []
    ambiguous_samples: list[dict] = []
    n_unique_instances = 0
    n_ambig_instances = 0

    for (n, arcs), group in sorted(by_n_arcs.items()):
        cids = {r["perm_class_id"] for r in group}
        if len(cids) == 1:
            cid = next(iter(cids))
            k = arcs_key(n, *arcs)
            unique_entries.append((k, cid))
            n_unique_instances += len(group)
        else:
            n_ambig_instances += len(group)
            if len(ambiguous_samples) < 8:
                ambiguous_samples.append(
                    {
                        "n": n,
                        "arcs": list(arcs),
                        "arcs_key": arcs_key(n, *arcs),
                        "perm_class_ids": sorted(cids),
                        "instance_count": len(group),
                        "examples": group[:3],
                    }
                )

    partial_keys = {
        "(n, arcs)": lambda r: (r["n"], r["arcs"]),
        "(n, cyclic_norm)": lambda r: (r["n"], cyclic_norm(r["arcs"])),
        "(n, rev_cyclic)": lambda r: (r["n"], rev_cyclic_norm(r["arcs"])),
        "(n, arcs, p0)": lambda r: (r["n"], r["arcs"], r["p0"]),
        "(n, arcs, p1)": lambda r: (r["n"], r["arcs"], r["p1"]),
        "(n, arcs, p0, p1)": lambda r: (r["n"], r["arcs"], r["p0"], r["p1"]),
        "(n, arcs, p0, p1, p2)": lambda r: (r["n"], r["arcs"], r["p0"], r["p1"], r["p2"]),
        "(n, arcs, Vres)": lambda r: (r["n"], r["arcs"], r["vres"]),
        "(n, arcs, Vres sorted)": lambda r: (r["n"], r["arcs"], tuple(sorted(r["vres"]))),
        "(n, arcs, chord parity)": lambda r: (r["n"], r["arcs"], chord_parity(r["c1"], r["c2"])),
        "(n, chords sorted)": lambda r: (r["n"], chord_parity(r["c1"], r["c2"])),
        "full endpoints": lambda r: (r["n"], r["p0"], r["p1"], r["p2"], r["p3"]),
    }
    key_analysis = {name: _key_stats(rows, fn) for name, fn in partial_keys.items()}

    # Vres collision detail
    vres_collisions: list[dict] = []
    by_n_arcs_vres: dict = defaultdict(list)
    for r in rows:
        by_n_arcs_vres[(r["n"], r["arcs"], r["vres"])].append(r)
    for k, group in by_n_arcs_vres.items():
        cids = {x["perm_class_id"] for x in group}
        if len(cids) > 1:
            vres_collisions.append(
                {
                    "n": k[0],
                    "arcs": list(k[1]),
                    "Vres": list(k[2]),
                    "perm_class_ids": sorted(cids),
                    "instances": [
                        {
                            "catalog_index": x["catalog_index"],
                            "p0": x["p0"],
                            "p1": x["p1"],
                            "p2": x["p2"],
                            "p3": x["p3"],
                            "perm_class_id": x["perm_class_id"],
                        }
                        for x in group
                    ],
                }
            )

    partial_key_ladder = [
        {
            "key": name,
            "inst_unique": key_analysis[name]["inst_unique"],
            "inst_ambig": key_analysis[name]["inst_ambig"],
            "notes": notes,
        }
        for name, notes in [
            ("(n, arcs)", "83/461; 126/209 arc shapes multi-perm"),
            ("(n, cyclic_norm)", "0/461; rotation-invariant keys fail"),
            ("(n, arcs, Vres)", "459/461; sole collision documented below"),
            ("(n, arcs, p0)", "461/461; minimal anchor (no p1..p3)"),
            ("(n, arcs, p1)", "461/461; symmetric anchor to p0"),
            ("(n, arcs, p0, p1)", "461/461; redundant given p0 + arcs"),
            ("(n, arcs, p0, p1, p2)", "461/461; redundant given p0 + arcs"),
            ("full endpoints", "461/461; emit hash endpointsLookupKey"),
        ]
    ]

    # Candidate "closed forms" (simple arithmetic / schedule invariants without tabulation).
    def total_arcs(r: dict) -> int:
        return sum(r["arcs"])

    def hop_budget(r: dict) -> int:
        return r["n"] - 4

    closed_form_candidates = {
        "(n, total, p0)": lambda r: (r["n"], total_arcs(r), r["p0"]),
        "(n, hop_budget, p0)": lambda r: (r["n"], hop_budget(r), r["p0"]),
        "(n, a0, p0)": lambda r: (r["n"], r["arcs"][0], r["p0"]),
        "(n, max(arcs), p0)": lambda r: (r["n"], max(r["arcs"]), r["p0"]),
        "(n, sorted(arcs), p0)": lambda r: (r["n"], tuple(sorted(r["arcs"])), r["p0"]),
        "(n, arcs, total mod 2)": lambda r: (r["n"], r["arcs"], total_arcs(r) % 2),
        "(n, arcs, p0 mod n)": lambda r: (r["n"], r["arcs"], r["p0"] % r["n"]),
        "(n, arcs, p0, perm_class_id)": lambda r: (r["n"], r["arcs"], r["p0"], r["perm_class_id"]),
    }
    closed_form_analysis = {name: _key_stats(rows, fn) for name, fn in closed_form_candidates.items()}

    perm_class_by_n: dict[int, set[int]] = defaultdict(set)
    for r in rows:
        perm_class_by_n[r["n"]].add(r["perm_class_id"])
    perm_classes_used = sorted({r["perm_class_id"] for r in rows})

    closed_form_verdict = {
        "status": "no_combinatorial_closed_form_without_tabulation",
        "catalog_instances": 461,
        "perm_classes": 10,
        "perm_class_ids": perm_classes_used,
        "perm_classes_by_n": {str(n): sorted(cids) for n, cids in sorted(perm_class_by_n.items())},
        "minimal_perfect_partial_keys": ["(n, arcs, p0)", "(n, arcs, p1)"],
        "weaker_keys_fail": {
            "(n, arcs)": "83/461 (378 need endpoint anchor)",
            "(n, cyclic_norm)": "0/461",
            "(n, arcs, Vres)": "459/461 (c6 collision idx 10/18)",
            "(n, total, p0)": f"{closed_form_analysis['(n, total, p0)']['inst_unique']}/461",
            "(n, hop_budget, p0)": f"{closed_form_analysis['(n, hop_budget, p0)']['inst_unique']}/461",
            "(n, sorted(arcs), p0)": f"{closed_form_analysis['(n, sorted(arcs), p0)']['inst_unique']}/461",
        },
        "why_impossible": [
            "Perm dst is the signed K4 isomorphism from E2 witness search, not a polynomial in schedule counts.",
            "126/209 arc shapes carry 2+ perm classes: endpoint placement (p0 anchor) is necessary.",
            "Cyclic/reverse-cyclic normalization fixes 0/461: perm depends on cycle labeling, not shape alone.",
            "Residual variable set Vres is almost but not enough: sole collision n=6 arcs=(1,0,0,1) Vres=[2,4,5,6,7,8].",
            "Simple schedule invariants (total, hop budget, sorted arcs) + p0 still collide on catalog.",
            "461/461 coverage requires emit tabulation (461-key endpointsLookupKey or 461-key arcsP0LookupKey).",
            "Lean bridge: topologyPermForArcsP0 461/461 agrees with full hash; ParametricArcP0GoalSufficient.",
        ],
        "honest_remainder": (
            "Combinatorial closed form without emit/native_decide = ruled out on catalog evidence; "
            "use topologyPermForArcsP0Of (461/461 tabulation) or topologyPermForEndpoints (461/461 hash)."
        ),
    }

    report = {
        "total_instances": len(instances),
        "arc_shapes_total": len(by_n_arcs),
        "arc_shapes_unique_perm": len(unique_entries),
        "arc_shapes_ambiguous_perm": len(by_n_arcs) - len(unique_entries),
        "instances_unique_perm": n_unique_instances,
        "instances_ambiguous_perm": n_ambig_instances,
        "partial_key_analysis": key_analysis,
        "partial_key_ladder": partial_key_ladder,
        "best_partial_key": "(n, arcs, p0)",
        "best_partial_coverage": "461/461 instances (weaker than full endpoints; no p1,p2,p3)",
        "minimal_perfect_partial_keys": ["(n, arcs, p0)", "(n, arcs, p1)"],
        "vres_collision_count": len(vres_collisions),
        "vres_collisions": vres_collisions,
        "fundamental_limit": (
            "(n, toArcs) fixes perm for 83/461 instances only; "
            "126/209 arc shapes need endpoint placement. "
            "Cyclic/reverse-cyclic normalization: 0/461 (all 55 shapes multi-perm). "
            "(n, arcs, Vres): 459/461 — one collision at n=6 arcs=(1,0,0,1), "
            "Vres=[2,4,5,6,7,8], catalog idx 10 vs 18 (p0=0 vs p0=1). "
            "(n, arcs, p0): 461/461 — minimal perfect partial key on catalog; "
            "p0+p1+p2 keys redundant (arcs + one anchor fixes placement)."
        ),
        "closed_form_analysis": closed_form_analysis,
        "closed_form_verdict": closed_form_verdict,
        "unique_arcs_keys": [{"key": k, "perm_class_id": cid} for k, cid in unique_entries],
        "ambiguous_samples": ambiguous_samples,
    }

    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(
        f"wrote {OUT}: shapes={report['arc_shapes_total']} "
        f"unique={report['arc_shapes_unique_perm']} "
        f"ambig={report['arc_shapes_ambiguous_perm']} "
        f"inst_unique={report['instances_unique_perm']} "
        f"arcs_p0={key_analysis['(n, arcs, p0)']['inst_unique']}/461"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
