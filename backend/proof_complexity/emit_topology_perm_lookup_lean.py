"""E5 point 2: emit closed-form CrossingEndpoints -> topology permutation lookup.

Reads `crossing_residual_catalog.json`, maps each instance to sorted endpoints
(n, p0, p1, p2, p3) and one of 10 catalog permutation classes, and writes
`lean/PNPLab/CrossingTopologyPermLookup.lean`.

Lookup: hash key n*10^4+p0*10^3+p1*10^2+p2*10+p3 -> perm class id 0..9 -> catalogPerm*.

Partial arcs lookup: (n, toArcs) key n*10^4+a0*10^3+... fixes perm for 83/461 instances
(83/209 arc shapes); 126 shapes ambiguous (378 instances) — endpoint tie-break required.

Stronger partial: (n, toArcs, p0) key n*10^5+a0*10^4+...+p0 fixes perm for 461/461
(weaker than full endpoints — no p1,p2,p3). Cyclic norm and (n,arcs,Vres) insufficient
(459/461; sole collision n=6 arcs=(1,0,0,1) Vres=[2,4,5,6,7,8] idx 10 vs 18).
"""

from __future__ import annotations

import json
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CATALOG = ROOT / "reports" / "discovery" / "crossing_residual_catalog.json"
OUT = ROOT / "lean" / "PNPLab" / "CrossingTopologyPermLookup.lean"

# Sorted by perm tuple; names match `CrossingEndpointsGlobalRename.lean`.
PERM_CLASSES: list[tuple[tuple[int, ...], str]] = [
    ((1, 2, 3, 4, 5, 6), "catalogPerm123456"),
    ((1, 2, 3, 4, 6, 5), "catalogPerm123465"),
    ((1, 2, 3, 5, 4, 6), "catalogPerm123546"),
    ((1, 2, 3, 5, 6, 4), "catalogPerm123564"),
    ((1, 2, 3, 6, 4, 5), "catalogPerm123645"),
    ((1, 2, 3, 6, 5, 4), "catalogPerm123654"),
    ((1, 2, 4, 5, 6, 3), "ofoldGlobalRenameDst"),
    ((1, 2, 4, 6, 5, 3), "catalogPerm124653"),
    ((1, 2, 5, 4, 6, 3), "catalogPerm125463"),
    ((1, 2, 6, 4, 5, 3), "catalogPerm126453"),
]
PERM_TO_ID = {p: i for i, (p, _) in enumerate(PERM_CLASSES)}


def endpoints_fields(n: int, c1: tuple[int, int], c2: tuple[int, int]) -> tuple[int, int, int, int]:
    pts = sorted({*c1, *c2})
    assert len(pts) == 4
    return pts[0], pts[1], pts[2], pts[3]


def hash_key(n: int, p0: int, p1: int, p2: int, p3: int) -> int:
    return n * 10000 + p0 * 1000 + p1 * 100 + p2 * 10 + p3


def arcs_key(n: int, a0: int, a1: int, a2: int, a3: int) -> int:
    return n * 10000 + a0 * 1000 + a1 * 100 + a2 * 10 + a3


def arcs_p0_key(n: int, a0: int, a1: int, a2: int, a3: int, p0: int) -> int:
    return n * 100000 + a0 * 10000 + a1 * 1000 + a2 * 100 + a3 * 10 + p0


def _emit_class_of_id() -> str:
    lines = ["def topologyPermClassOfId (id : Nat) : List Nat := match id with"]
    for i, (_, name) in enumerate(PERM_CLASSES):
        lines.append(f"  | {i} => {name}")
    lines.append(f"  | _ => {PERM_CLASSES[0][1]}")
    lines.extend(
        [
            "",
            "theorem topologyPermClassOfId_len (id : Nat) : (topologyPermClassOfId id).length = 6 := by",
            "  unfold topologyPermClassOfId",
            "  split <;> native_decide",
        ]
    )
    return "\n".join(lines)


def _emit_key_match(entries: list[tuple[int, int]]) -> str:
    lines = ["def topologyPermClassIdOfKey (key : Nat) : Nat :="]
    by_n: dict[int, list[tuple[int, int]]] = {}
    for key, cid in entries:
        n = key // 10000
        by_n.setdefault(n, []).append((key, cid))
    lines.append("  match key with")
    for n in sorted(by_n):
        for key, cid in sorted(by_n[n]):
            lines.append(f"  | {key} => {cid}")
    lines.append("  | _ => 0")
    return "\n".join(lines)


def _emit_arcs_key_match(entries: list[tuple[int, int]]) -> str:
    lines = ["def topologyPermClassIdOfArcsKey (key : Nat) : Option Nat :="]
    by_n: dict[int, list[tuple[int, int]]] = {}
    for key, cid in entries:
        n = key // 10000
        by_n.setdefault(n, []).append((key, cid))
    lines.append("  match key with")
    for n in sorted(by_n):
        for key, cid in sorted(by_n[n]):
            lines.append(f"  | {key} => some {cid}")
    lines.append("  | _ => none")
    return "\n".join(lines)


def _emit_arcs_agreement_flags(unique_catalog_indices: list[tuple[int, int, int, int, int, int]]) -> str:
    agreement_flags = [
        f"  (decide (topologyPermForArcs {n} "
        f"{{ a0 := {a0}, a1 := {a1}, a2 := {a2}, a3 := {a3} }} "
        f"= some (topologyPermForCatalogIndex ⟨{idx}, by decide⟩)))"
        for idx, n, a0, a1, a2, a3 in unique_catalog_indices
    ]
    return "\n".join(
        [
            "/-- All 83 arcs-unique catalog instances: arcs partial fn agrees with catalog index. -/",
            "def topologyPermArcsAgreementFlags : List Bool :=",
            "  [",
            ",\n".join(agreement_flags),
            "  ]",
            "",
            "theorem topologyPermArcsAgreementFlags_all :",
            "    topologyPermArcsAgreementFlags.all id = true := by",
            "  native_decide",
        ]
    )


def _emit_arcs_p0_key_match(entries: list[tuple[int, int]]) -> str:
    lines = ["def topologyPermClassIdOfArcsP0Key (key : Nat) : Nat :="]
    by_n: dict[int, list[tuple[int, int]]] = {}
    for key, cid in entries:
        n = key // 100000
        by_n.setdefault(n, []).append((key, cid))
    lines.append("  match key with")
    for n in sorted(by_n):
        for key, cid in sorted(by_n[n]):
            lines.append(f"  | {key} => {cid}")
    lines.append("  | _ => 0")
    return "\n".join(lines)


def _emit_arcs_p0_section(all_rows: list[tuple[int, int, int, int, int, int, int, int, int, int]]) -> str:
    """Emit (n, toArcs, p0) lookup — 461/461 instances, no p1..p3."""
    entries = [(arcs_p0_key(n, a0, a1, a2, a3, p0), cid) for n, p0, _p1, _p2, _p3, a0, a1, a2, a3, cid in all_rows]
    entries.sort()
    assert len(entries) == len(set(entries)) == 461
    return "\n".join(
        [
            "/-- Compact `(n, toArcs, p0)` hash; fixes perm on all 461 catalog instances. -/",
            "def arcsP0LookupKey (n : Nat) (c : CrossingArcs) (p0 : Nat) : Nat :=",
            "  n * 100000 + c.a0 * 10000 + c.a1 * 1000 + c.a2 * 100 + c.a3 * 10 + p0",
            "",
            _emit_arcs_p0_key_match(entries),
            "",
            "/-- `(n, toArcs, p0)` determines perm class (461/461; weaker than full endpoints). -/",
            "def topologyPermForArcsP0 (n : Nat) (c : CrossingArcs) (p0 : Nat) : List Nat :=",
            "  topologyPermClassOfId (topologyPermClassIdOfArcsP0Key (arcsP0LookupKey n c p0))",
            "",
            "theorem topologyPermForArcsP0_len (n : Nat) (c : CrossingArcs) (p0 : Nat) :",
            "    (topologyPermForArcsP0 n c p0).length = 6 :=",
            "  topologyPermClassOfId_len _",
            "",
            "/-- Endpoint wrapper: uses `e.p0` only (not p1..p3). -/",
            "def topologyPermForArcsP0Of (e : CrossingEndpoints) : List Nat :=",
            "  topologyPermForArcsP0 e.n e.toArcs e.p0",
            "",
            "theorem topologyPermForArcsP0Of_eq (e : CrossingEndpoints) :",
            "    topologyPermForArcsP0Of e = topologyPermForArcsP0 e.n e.toArcs e.p0 :=",
            "  rfl",
            "",
            "theorem topologyPermForArcsP0Of_c5Ofold :",
            "    topologyPermForArcsP0Of c5OfoldEndpoints = ofoldGlobalRenameDst := by",
            "  native_decide",
            "",
            "theorem topologyPermForArcsP0Of_c5Alt1 :",
            "    topologyPermForArcsP0Of c5Alt1Endpoints = catalogPerm123456 := by",
            "  native_decide",
            "",
            "theorem topologyPermForArcsP0Of_c6 :",
            "    topologyPermForArcsP0Of c6Endpoints0123 = ofoldGlobalRenameDst := by",
            "  native_decide",
        ]
    )


def _emit_arcs_p0_endpoint_agreement(
    all_rows: list[tuple[int, int, int, int, int, int, int, int, int, int]],
) -> str:
    flags = [
        f"  (decide (topologyPermForArcsP0 {n} "
        f"{{ a0 := {a0}, a1 := {a1}, a2 := {a2}, a3 := {a3} }} {p0} "
        f"= topologyPermForEndpoints "
        f"{{ n := {n}, p0 := {p0}, p1 := {p1}, p2 := {p2}, p3 := {p3}, "
        f"ordered := by decide }}))"
        for n, p0, p1, p2, p3, a0, a1, a2, a3, _cid in all_rows
    ]
    return "\n".join(
        [
            "/-- All 461 catalog instances: `(n, toArcs, p0)` agrees with endpoint hash. -/",
            "def topologyPermArcsP0EndpointAgreementFlags : List Bool :=",
            "  [",
            ",\n".join(flags),
            "  ]",
            "",
            "theorem topologyPermArcsP0EndpointAgreementFlags_all :",
            "    topologyPermArcsP0EndpointAgreementFlags.all id = true := by",
            "  native_decide",
            "",
            "/-- 461/461: `(n, toArcs, p0)` partial lookup matches full endpoint hash (emit-checked). -/",
            "theorem topologyPermArcsP0EndpointAgreementFlags_mass :",
            "    topologyPermArcsP0EndpointAgreementFlags.length = 461 ∧",
            "      topologyPermArcsP0EndpointAgreementFlags.all id = true := by",
            "  native_decide",
        ]
    )


def _emit_vres_collision_section() -> str:
    """Emit certified Vres-collision witness (459/461 limit for (n,arcs,Vres) key)."""
    return "\n".join(
        [
            "/-- Catalog's sole `(n, toArcs, Vres)` collision: n=6, arcs=(1,0,0,1), Vres=[2,4,5,6,7,8].",
            "    Witnesses `c6Endpoints0234` (catalog idx 10, p0=0) vs `c6Endpoints1345` (idx 18, p0=1).",
            "    `(n, toArcs, p0)` resolves; see `topologyPermArcsVresCollision_p0_resolves`. -/",
            "theorem topologyPermArcsVresCollision_same_arcs :",
            "    c6Endpoints0234.toArcs.a0 = c6Endpoints1345.toArcs.a0 ∧",
            "      c6Endpoints0234.toArcs.a1 = c6Endpoints1345.toArcs.a1 ∧",
            "      c6Endpoints0234.toArcs.a2 = c6Endpoints1345.toArcs.a2 ∧",
            "      c6Endpoints0234.toArcs.a3 = c6Endpoints1345.toArcs.a3 := by",
            "  native_decide",
            "",
            "theorem topologyPermArcsVresCollision_same_vres :",
            "    residualGlobalVres c6Endpoints0234 = residualGlobalVres c6Endpoints1345 := by",
            "  native_decide",
            "",
            "theorem topologyPermArcsVresCollision_same_vres_list :",
            "    residualGlobalVres c6Endpoints0234 = [2, 4, 5, 6, 7, 8] := by",
            "  native_decide",
            "",
            "theorem topologyPermArcsVresCollision_diff_perm :",
            "    topologyPermForEndpoints c6Endpoints0234 = catalogPerm124653 ∧",
            "      topologyPermForEndpoints c6Endpoints1345 = catalogPerm123654 ∧",
            "      topologyPermForEndpoints c6Endpoints0234 ≠ topologyPermForEndpoints c6Endpoints1345 := by",
            "  native_decide",
            "",
            "theorem topologyPermArcsVresCollision_arcs_none :",
            "    topologyPermForArcsOf c6Endpoints0234 = none ∧",
            "      topologyPermForArcsOf c6Endpoints1345 = none := by",
            "  native_decide",
            "",
            "theorem topologyPermArcsVresCollision_p0_resolves :",
            "    topologyPermForArcsP0Of c6Endpoints0234 = catalogPerm124653 ∧",
            "      topologyPermForArcsP0Of c6Endpoints1345 = catalogPerm123654 ∧",
            "      topologyPermForArcsP0Of c6Endpoints0234 ≠ topologyPermForArcsP0Of c6Endpoints1345 := by",
            "  native_decide",
            "",
            "def topologyPermArcsVresCollisionDoc : String :=",
            '  "459/461: (n,toArcs,Vres) insufficient; sole collision n=6 arcs=(1,0,0,1) " ++',
            '  "Vres=[2,4,5,6,7,8] idx10/18; p0 anchor resolves (461/461 via topologyPermForArcsP0)"',
        ]
    )


def _emit_arcs_endpoint_agreement(
    unique_endpoint_rows: list[tuple[int, int, int, int, int, int, int, int, int, int]],
) -> str:
    """Emit checks: arcs partial fn = some (topologyPermForEndpoints e) on unique shapes."""
    flags = [
        f"  (decide (topologyPermForArcs {n} "
        f"{{ a0 := {a0}, a1 := {a1}, a2 := {a2}, a3 := {a3} }} "
        f"= some (topologyPermForEndpoints "
        f"{{ n := {n}, p0 := {p0}, p1 := {p1}, p2 := {p2}, p3 := {p3}, "
        f"ordered := by decide }})))"
        for n, p0, p1, p2, p3, a0, a1, a2, a3 in unique_endpoint_rows
    ]
    return "\n".join(
        [
            "/-- Arcs-unique shapes: partial lookup matches full endpoint hash lookup. -/",
            "def topologyPermArcsEndpointAgreementFlags : List Bool :=",
            "  [",
            ",\n".join(flags),
            "  ]",
            "",
            "theorem topologyPermArcsEndpointAgreementFlags_all :",
            "    topologyPermArcsEndpointAgreementFlags.all id = true := by",
            "  native_decide",
        ]
    )


def _emit_arcs_section(
    unique_arcs: list[tuple[int, int]],
    n_shapes: int,
    n_unique_shapes: int,
    n_ambig_shapes: int,
    n_unique_inst: int,
    n_ambig_inst: int,
) -> str:
    lines = [
        "/-- Compact `(n, toArcs)` hash; unique perm only on 83/209 arc shapes. -/",
        "def arcsShapeLookupKey (n : Nat) (c : CrossingArcs) : Nat :=",
        "  n * 10000 + c.a0 * 1000 + c.a1 * 100 + c.a2 * 10 + c.a3",
        "",
        _emit_arcs_key_match(unique_arcs),
        "",
        "/-- Partial: `some` iff `(n, toArcs)` carries a unique perm class (83/461 instances). -/",
        "def topologyPermForArcs (n : Nat) (c : CrossingArcs) : Option (List Nat) :=",
        "  (topologyPermClassIdOfArcsKey (arcsShapeLookupKey n c)).map topologyPermClassOfId",
        "",
        "theorem topologyPermForArcs_some_len {n : Nat} {c : CrossingArcs} {p : List Nat}",
        "    (h : topologyPermForArcs n c = some p) : p.length = 6 := by",
        "  unfold topologyPermForArcs at h",
        "  cases hkey : topologyPermClassIdOfArcsKey (arcsShapeLookupKey n c) with",
        "  | none => simp [hkey] at h",
        "  | some id =>",
        "    simp [hkey] at h",
        "    subst h",
        "    exact topologyPermClassOfId_len id",
        "",
        "/-- Arc shape has a unique catalog perm class (83/209 shapes; 83/461 instances). -/",
        "def topologyPermArcShapeUnique (n : Nat) (c : CrossingArcs) : Prop :=",
        "  (topologyPermForArcs n c).isSome",
        "",
        "theorem topologyPermArcShapeUnique_iff (n : Nat) (c : CrossingArcs) :",
        "    topologyPermArcShapeUnique n c ↔ (topologyPermForArcs n c).isSome :=",
        "  Iff.rfl",
        "",
        "def topologyPermArcShapeMass : Nat × Nat × Nat × Nat × Nat :=",
        f"  ({n_shapes}, {n_unique_shapes}, {n_ambig_shapes}, {n_unique_inst}, {n_ambig_inst})",
        "",
        "theorem topologyPermArcShapeMass_eq :",
        f"    topologyPermArcShapeMass = ({n_shapes}, {n_unique_shapes}, {n_ambig_shapes}, "
        f"{n_unique_inst}, {n_ambig_inst}) :=",
        "  rfl",
        "",
        "theorem topologyPermArcShapeMass_native :",
        f"    topologyPermArcShapeMass = ({n_shapes}, {n_unique_shapes}, {n_ambig_shapes}, "
        f"{n_unique_inst}, {n_ambig_inst}) := by",
        "  native_decide",
        "",
        "theorem topologyPermForArcs_c5Alt1_some :",
        "    topologyPermForArcs 5 c5Alt1Endpoints.toArcs = some catalogPerm123456 := by",
        "  native_decide",
        "",
        "theorem topologyPermForArcs_c5Ofold_none :",
        "    topologyPermForArcs 5 c5OfoldEndpoints.toArcs = none := by",
        "  native_decide",
        "",
        "theorem topologyPermForArcs_c6_none :",
        "    topologyPermForArcs 6 c6Endpoints0123.toArcs = none := by",
        "  native_decide",
        "",
        "/-- Endpoint wrapper for the partial arcs lookup. -/",
        "def topologyPermForArcsOf (e : CrossingEndpoints) : Option (List Nat) :=",
        "  topologyPermForArcs e.n e.toArcs",
        "",
        "theorem topologyPermForArcsOf_eq (e : CrossingEndpoints) :",
        "    topologyPermForArcsOf e = topologyPermForArcs e.n e.toArcs :=",
        "  rfl",
        "",
        "theorem topologyPermForArcsOf_some_iff (e : CrossingEndpoints) (p : List Nat) :",
        "    topologyPermForArcsOf e = some p ↔ topologyPermForArcs e.n e.toArcs = some p :=",
        "  Iff.rfl",
        "",
        "theorem topologyPermArcShapeUnique_ofArcsOf (e : CrossingEndpoints) :",
        "    topologyPermArcShapeUnique e.n e.toArcs ↔ (topologyPermForArcsOf e).isSome := by",
        "  simp [topologyPermArcShapeUnique, topologyPermForArcsOf]",
    ]
    return "\n".join(lines)


def _emit_catalog_index_class_ids(
    entries: list[tuple[int, int, int, int, int, int, int]],
) -> str:
    lines = [
        "def topologyPermClassIdForCatalogIndex (i : Fin 461) : Nat :=",
        "  match i.val with",
    ]
    for idx, _n, _p0, _p1, _p2, _p3, cid in entries:
        lines.append(f"  | {idx} => {cid}")
    lines.extend(
        [
            "  | _ => 0",
            "",
            "def topologyPermForCatalogIndex (i : Fin 461) : List Nat :=",
            "  topologyPermClassOfId (topologyPermClassIdForCatalogIndex i)",
            "",
            "theorem topologyPermForCatalogIndex_len (i : Fin 461) :",
            "    (topologyPermForCatalogIndex i).length = 6 :=",
            "  topologyPermClassOfId_len _",
        ]
    )
    return "\n".join(lines)


def _emit_smoke_theorems(smokes: list[tuple[str, int, int, int, int, int, int]]) -> str:
    lines = []
    for name, _n, _p0, _p1, _p2, _p3, cid in smokes:
        perm_name = PERM_CLASSES[cid][1]
        lines.append(
            f"theorem topologyPerm_{name}_eq :\n"
            f"    topologyPermForEndpoints {name} = {perm_name} := by\n"
            f"  native_decide"
        )
    return "\n".join(lines)


def main() -> int:
    catalog = json.loads(CATALOG.read_text(encoding="utf-8"))
    instances = catalog["instances"]
    assert len(instances) == 461 == catalog["iso_ok"]

    key_entries: list[tuple[int, int]] = []
    catalog_entries: list[tuple[int, int, int, int, int, int, int]] = []
    all_arcs_p0_rows: list[tuple[int, int, int, int, int, int, int, int, int, int]] = []
    by_n_arcs: dict[tuple[int, tuple[int, int, int, int]], list[tuple[int, int]]] = defaultdict(list)

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
        k = hash_key(n, p0, p1, p2, p3)
        key_entries.append((k, cid))
        catalog_entries.append((i, n, p0, p1, p2, p3, cid))
        all_arcs_p0_rows.append((n, p0, p1, p2, p3, a0, a1, a2, a3, cid))
        by_n_arcs[(n, arcs)].append((i, cid))

    assert len(key_entries) == len(set(key_entries)) == 461
    assert len({e[6] for e in catalog_entries}) == 10
    key_entries.sort()

    unique_arcs: list[tuple[int, int]] = []
    unique_catalog_indices: list[tuple[int, int, int, int, int, int]] = []
    unique_endpoint_rows: list[tuple[int, int, int, int, int, int, int, int, int, int]] = []
    n_unique_inst = 0
    n_ambig_inst = 0

    for (n, arcs), rows in sorted(by_n_arcs.items()):
        cids = {cid for _i, cid in rows}
        if len(cids) == 1:
            cid = next(iter(cids))
            k = arcs_key(n, *arcs)
            unique_arcs.append((k, cid))
            assert len(rows) == 1
            idx, _ = rows[0]
            unique_catalog_indices.append((idx, n, *arcs))
            inst = instances[idx]
            c1, c2 = tuple(inst["chords"][0]), tuple(inst["chords"][1])
            p0, p1, p2, p3 = endpoints_fields(n, c1, c2)
            unique_endpoint_rows.append((n, p0, p1, p2, p3, *arcs))
            n_unique_inst += 1
        else:
            n_ambig_inst += len(rows)

    n_shapes = len(by_n_arcs)
    n_unique_shapes = len(unique_arcs)
    n_ambig_shapes = n_shapes - n_unique_shapes
    assert n_unique_inst == 83
    assert n_ambig_inst == 378
    assert n_unique_shapes == 83
    assert n_ambig_shapes == 126

    smokes = [
        ("c5OfoldEndpoints", 5, 0, 1, 2, 3, PERM_TO_ID[(1, 2, 4, 5, 6, 3)]),
        ("c5Alt1Endpoints", 5, 0, 1, 2, 4, PERM_TO_ID[(1, 2, 3, 4, 5, 6)]),
        ("c6Endpoints0123", 6, 0, 1, 2, 3, PERM_TO_ID[(1, 2, 4, 5, 6, 3)]),
    ]

    arcs_section = _emit_arcs_section(
        unique_arcs,
        n_shapes,
        n_unique_shapes,
        n_ambig_shapes,
        n_unique_inst,
        n_ambig_inst,
    )
    arcs_p0_section = _emit_arcs_p0_section(all_arcs_p0_rows)
    arcs_agreement = _emit_arcs_agreement_flags(unique_catalog_indices)
    arcs_endpoint_agreement = _emit_arcs_endpoint_agreement(unique_endpoint_rows)
    arcs_p0_endpoint_agreement = _emit_arcs_p0_endpoint_agreement(all_arcs_p0_rows)

    body = f"""/-
  E5 point 2: closed-form `CrossingEndpoints` -> E2 topology permutation dst.

  Hash key n*10^4+p0*10^3+p1*10^2+p2*10+p3 maps 461 unique endpoint tuples to one of
  10 catalog permutation classes (`catalogPerm*` / `ofoldGlobalRenameDst`).

  **Honest limit:** `(n, toArcs)` alone fixes perm for **83/461** instances only
  ({n_unique_shapes}/{n_shapes} arc shapes unique; {n_ambig_shapes} ambiguous shapes
  cover {n_ambig_inst} instances). Cyclic normalization and `(n, arcs, Vres)` also
  insufficient (459/461; sole collision n=6 arcs=(1,0,0,1), Vres=[2,4,5,6,7,8],
  catalog idx 10 vs 18 — see `topologyPermArcsVresCollision_*`). **Stronger partial:**
  `(n, toArcs, p0)` fixes perm for **461/461** (weaker than full endpoints — no p1..p3).
  `(n, toArcs, p1)` also 461/461; p0+p1+p2 keys redundant. Smokes c5Ofold/c6 are
  arcs-ambiguous but arcs+p0-unique. Full hash `endpointsLookupKey` equivalent.

  **No combinatorial closed form without tabulation:** perm dst is E2 signed K4 iso;
  simple schedule invariants (total, hop budget, sorted arcs) + p0 still collide on
  catalog; see `topologyPermNoClosedFormDoc` and
  `reports/discovery/topology_perm_arcs_analysis.json` (`closed_form_verdict`).

  Generated by `backend/proof_complexity/emit_topology_perm_lookup_lean.py`.
  Analysis: `backend/proof_complexity/analyze_topology_perm_arcs.py`.
  Source: `reports/discovery/crossing_residual_catalog.json` ({len(instances)}/461 iso).
-/

import PNPLab.CrossingEndpointsGlobalRename

namespace PNPLab.Bicyclic

open PNPLab.Resolution

/-- Compact endpoint hash (461 unique keys on n=5..10 mass window). -/
def endpointsLookupKey (e : CrossingEndpoints) : Nat :=
  e.n * 10000 + e.p0 * 1000 + e.p1 * 100 + e.p2 * 10 + e.p3

{_emit_class_of_id()}

{_emit_key_match(key_entries)}

def topologyPermClassId (e : CrossingEndpoints) : Nat :=
  topologyPermClassIdOfKey (endpointsLookupKey e)

/-- Closed-form permutation dst for residual global topology rename. -/
def topologyPermForEndpoints (e : CrossingEndpoints) : List Nat :=
  topologyPermClassOfId (topologyPermClassId e)

theorem topologyPermForEndpoints_len (e : CrossingEndpoints) :
    (topologyPermForEndpoints e).length = 6 :=
  topologyPermClassOfId_len _

def globalTopologyRenameFor (e : CrossingEndpoints)
    (hsrc : (residualGlobalVres e).length = 6) : VarRename :=
  globalTopologyRenameFromPerm e (topologyPermForEndpoints e) hsrc
    (topologyPermForEndpoints_len e)

theorem globalTopologyRenameFor_eq_perm (e : CrossingEndpoints)
    (hsrc : (residualGlobalVres e).length = 6) :
    globalTopologyRenameFor e hsrc =
      globalTopologyRenameFromPerm e (topologyPermForEndpoints e) hsrc
        (topologyPermForEndpoints_len e) :=
  rfl

{arcs_section}

{arcs_p0_section}

{_emit_catalog_index_class_ids(catalog_entries)}

{arcs_agreement}

{arcs_endpoint_agreement}

{arcs_p0_endpoint_agreement}

{_emit_vres_collision_section()}

{_emit_smoke_theorems(smokes)}

/-- Partial-key ladder + p0 agreement (461/461); emit-checked catalog summary. -/
theorem topologyPermPartialKeyMass_bundle :
    topologyPermArcShapeMass = ({n_shapes}, {n_unique_shapes}, {n_ambig_shapes}, {n_unique_inst}, {n_ambig_inst}) ∧
      topologyPermArcsP0EndpointAgreementFlags.length = 461 ∧
      topologyPermArcsP0EndpointAgreementFlags.all id = true := by
  native_decide

def topologyPermPartialKeyLadderDoc : String :=
  "(n,toArcs) 83/461; cyclic 0/461; (n,toArcs,Vres) 459/461; " ++
  "(n,toArcs,p0) 461/461 minimal; full endpointsLookupKey 461/461 emit"

def topologyPermNoClosedFormDoc : String :=
  "No combinatorial closed form without emit tabulation on catalog: perm dst = E2 signed " ++
  "K4 iso witness; 126/209 arc shapes multi-perm; Vres collision c6 idx10/18; " ++
  "schedule invariants (total,hop,sorted arcs)+p0 insufficient; use topologyPermForArcsP0Of " ++
  "461/461 or topologyPermForEndpoints 461/461 hash"

def topologyPermLookupDoc : String :=
  "E5: endpointsLookupKey→10 perm classes; topologyPermForArcs partial (83/461); " ++
  "topologyPermForArcsP0 (461/461, weaker key); Vres collision 459/461 (c6Endpoints0234/1345); " ++
  "no closed form without tabulation; topologyPermForEndpoints / catalog index"

theorem topologyPermForCatalogIndex_all_len :
    ∀ i : Fin 461, (topologyPermForCatalogIndex i).length = 6 :=
  topologyPermForCatalogIndex_len

end PNPLab.Bicyclic

namespace PNPLab.Resolution

open Bicyclic

theorem topology_perm_catalog_mass :
    crossingResidualCatalogMass.isoOk = 461 ∧
      crossingResidualCatalogMass.flipNeeded = 0 := by
  native_decide

end PNPLab.Resolution
"""
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(body, encoding="utf-8")
    print(
        f"wrote {OUT} keys={len(key_entries)} perm_classes={len(PERM_CLASSES)} "
        f"arcs_unique={n_unique_shapes}/{n_shapes}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
