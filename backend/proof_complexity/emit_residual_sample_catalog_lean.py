"""Emit Lean stratified residual sample catalog (G5 beyond packs + alts).

Picks ≥16 distinct non-canonical instances per hop budget 1..6 from the E2
catalog (~96 total; hop-1 has only 3 non-excluded crossings so surplus
samples cascade to later hops), recomputes residuals, and emits topology
set-eq witnesses via native_decide (no full LinkedChain projection chains).

Pins the prior 48 ResidualSampleCatalog samples and fills remaining slots
without duplicating canons, alts, or those forty-eight.
"""

from __future__ import annotations

import json
from collections import defaultdict
from pathlib import Path

from backend.proof_complexity.emit_crossing_residual_catalog import (
    _clause_set,
    _extract_k4_axioms,
    _find_signed_iso,
    residual_of,
)

ROOT = Path(__file__).resolve().parents[2]
CATALOG = ROOT / "reports" / "discovery" / "crossing_residual_catalog.json"
OUT = ROOT / "lean" / "PNPLab" / "ResidualSampleCatalog.lean"

# Canonical emit_*fold packs (exclude from sample).
CANONS = [
    (5, (0, 2), (1, 3)),
    (6, (0, 3), (2, 5)),
    (7, (0, 4), (1, 5)),
    (8, (0, 4), (1, 5)),
    (9, (0, 5), (1, 6)),
    (10, (0, 2), (1, 3)),
]

# AltResidualWitnesses (exclude from sample).
ALTS = [
    (5, (0, 2), (1, 4)),
    (6, (0, 2), (1, 3)),
    (7, (0, 2), (1, 3)),
    (8, (0, 2), (1, 3)),
    (9, (0, 2), (1, 3)),
    (10, (0, 2), (1, 4)),
]

# Prior ResidualSampleCatalog.lean (pin + exclude from new picks).
PREVIOUS_SAMPLES = [
    (5, (0, 3), (1, 4)),
    (5, (0, 3), (2, 4)),
    (5, (1, 3), (2, 4)),
    (6, (0, 2), (1, 4)),
    (6, (0, 2), (1, 5)),
    (6, (0, 3), (1, 4)),
    (6, (0, 3), (1, 5)),
    (6, (0, 3), (2, 4)),
    (6, (0, 4), (1, 5)),
    (6, (0, 4), (2, 5)),
    (6, (0, 4), (3, 5)),
    (6, (1, 3), (2, 4)),
    (6, (1, 3), (2, 5)),
    (6, (1, 4), (2, 5)),
    (6, (1, 4), (3, 5)),
    (6, (2, 4), (3, 5)),
    (7, (0, 2), (1, 4)),
    (7, (0, 2), (1, 5)),
    (7, (0, 2), (1, 6)),
    (7, (0, 3), (1, 4)),
    (7, (0, 3), (1, 5)),
    (7, (0, 3), (1, 6)),
    (7, (0, 3), (2, 4)),
    (7, (0, 3), (2, 5)),
    (8, (0, 2), (1, 4)),
    (8, (0, 2), (1, 5)),
    (8, (0, 2), (1, 6)),
    (8, (0, 2), (1, 7)),
    (8, (0, 3), (1, 4)),
    (8, (0, 3), (1, 5)),
    (8, (0, 3), (1, 6)),
    (8, (0, 3), (1, 7)),
    (9, (0, 2), (1, 4)),
    (9, (0, 2), (1, 5)),
    (9, (0, 2), (1, 6)),
    (9, (0, 2), (1, 7)),
    (9, (0, 2), (1, 8)),
    (9, (0, 3), (1, 4)),
    (9, (0, 3), (1, 5)),
    (9, (0, 3), (1, 6)),
    (10, (0, 2), (1, 5)),
    (10, (0, 2), (1, 6)),
    (10, (0, 2), (1, 7)),
    (10, (0, 2), (1, 8)),
    (10, (0, 2), (1, 9)),
    (10, (0, 3), (1, 4)),
    (10, (0, 3), (1, 5)),
    (10, (0, 3), (1, 6)),
]

EXCLUDED = set(CANONS + ALTS + PREVIOUS_SAMPLES)
PER_TIP = 16
TARGET_TOTAL = PER_TIP * 6


def _inst_key(n: int, c1: tuple[int, int], c2: tuple[int, int]) -> tuple:
    return (n, c1, c2)


def _inst_key_from_json(inst: dict) -> tuple:
    c1, c2 = inst["chords"]
    return _inst_key(inst["n"], tuple(c1), tuple(c2))


def _inst_lookup(instances: list[dict]) -> dict[tuple, dict]:
    return {_inst_key_from_json(inst): inst for inst in instances}


def _fill_bucket(
    pool: list[dict], need: int, seen: set[tuple]
) -> list[dict]:
    bucket: list[dict] = []
    for n in sorted({i["n"] for i in pool}):
        for inst in pool:
            k = _inst_key_from_json(inst)
            if inst["n"] == n and k not in seen:
                bucket.append(inst)
                seen.add(k)
                break
        if len(bucket) >= need:
            break
    for inst in pool:
        k = _inst_key_from_json(inst)
        if k not in seen:
            bucket.append(inst)
            seen.add(k)
        if len(bucket) >= need:
            break
    return bucket[:need]


def pick_stratified_sample(instances: list[dict]) -> list[dict]:
    """At least PER_TIP per tips 1..6; pin PREVIOUS_SAMPLES first."""
    lookup = _inst_lookup(instances)
    pinned: dict[int, list[dict]] = defaultdict(list)
    for key in PREVIOUS_SAMPLES:
        inst = lookup.get(key)
        if inst is None:
            raise ValueError(f"prior sample missing from catalog: {key}")
        pinned[inst["tips"]].append(inst)

    by_tips: dict[int, list[dict]] = defaultdict(list)
    for inst in instances:
        if _inst_key_from_json(inst) in EXCLUDED:
            continue
        by_tips[inst["tips"]].append(inst)

    picked: list[dict] = []
    seen: set[tuple] = set(_inst_key_from_json(i) for i in sum(pinned.values(), []))
    shortfall = 0
    for tips in range(1, 7):
        bucket = list(pinned.get(tips, []))
        need = max(0, PER_TIP - len(bucket))
        if need:
            pool = by_tips.get(tips, [])
            added = _fill_bucket(pool, need, seen)
            bucket.extend(added)
        cap = len(pinned.get(tips, [])) + len(by_tips.get(tips, []))
        if len(bucket) < PER_TIP:
            shortfall += PER_TIP - len(bucket)
        if len(bucket) < min(PER_TIP, cap):
            raise ValueError(
                f"tips={tips}: only {len(bucket)} samples after fill "
                f"(target {PER_TIP}, cap {cap})"
            )
        picked.extend(bucket)
        if tips == 2 and shortfall:
            pool = by_tips.get(2, [])
            surplus = _fill_bucket(pool, shortfall, seen)
            picked.extend(surplus)
            shortfall -= len(surplus)

    for tips in range(3, 7):
        if shortfall <= 0:
            break
        pool = by_tips.get(tips, [])
        surplus = _fill_bucket(pool, shortfall, seen)
        picked.extend(surplus)
        shortfall -= len(surplus)

    if shortfall:
        raise ValueError(
            f"could not fill {shortfall} surplus slots "
            f"(got {len(picked)}/{TARGET_TOTAL})"
        )
    assert len(picked) == TARGET_TOTAL, len(picked)
    return picked


def lean_clause(c: list[int] | tuple[int, ...]) -> str:
    if not c:
        return "[]"
    return "[" + ", ".join(f"({lit} : Lit)" for lit in c) + "]"


def list_clauses(name: str, clauses: list) -> str:
    lines = [f"def {name} : List Clause :="]
    for i, c in enumerate(clauses):
        pref = "  [ " if i == 0 else "  , "
        lines.append(pref + lean_clause(c))
    lines.append("  ]")
    return "\n".join(lines)


def main() -> int:
    catalog = json.loads(CATALOG.read_text(encoding="utf-8"))
    sample = pick_stratified_sample(catalog["instances"])
    assert len(sample) == TARGET_TOTAL, len(sample)

    k4 = _extract_k4_axioms()
    target = _clause_set(k4)
    blocks: list[str] = []
    names: list[str] = []

    for idx, inst in enumerate(sample, start=1):
        n = inst["n"]
        c1, c2 = inst["chords"]
        c1t, c2t = tuple(c1), tuple(c2)
        tips = inst["tips"]
        pre = f"samp{idx}"

        res = residual_of(n, c1t, c2t)
        assert res["shape_ok"] and res["tips"] == tips
        wit = _find_signed_iso(res["RAxioms"], res["Vres"], target)
        assert wit is not None and not wit["needs_flips"], (
            f"{pre} n={n} chords=({c1},{c2})"
        )

        names.append(pre)
        vres = "[" + ", ".join(str(v) for v in res["Vres"]) + "]"
        perm = "[" + ", ".join(str(v) for v in wit["permutation"]) + "]"
        blocks.append(
            f"""
/-- Sample hop-{tips}: C_{n} + {list(c1)},{list(c2)}. -/
def {pre}Vres : List Nat := {vres}
{list_clauses(pre + "RAxioms", res["RAxioms"])}
abbrev {pre}RClosed : List Clause := {pre}RAxioms

theorem {pre}R_size : {pre}RClosed.length = 16 := by native_decide
theorem {pre}Vres_len : {pre}Vres.length = 6 := by native_decide
theorem {pre}R_no_empty : ¬ ([] ∈ {pre}RClosed) := by native_decide

def {pre}TopologyRename : VarRename where
  src := {pre}Vres
  dst := {perm}
  src_len := {pre}Vres_len
  dst_len := by native_decide

def {pre}TopologySetEq : Bool :=
  renamedSubset {pre}TopologyRename {pre}RClosed k4Closed &&
    renamedSurjective {pre}TopologyRename {pre}RClosed k4Closed

theorem {pre}TopologySetEq_true : {pre}TopologySetEq = true := by native_decide
"""
        )

    body = f"""/-
  Stratified residual sample catalog (Category C / G5).

  {len(sample)} non-canonical crossings (≥{PER_TIP} per hop budget 3..6, thirteen
  at hop-2 and three at hop-1 — catalog caps; surplus cascades), each with
  topology set-eq to `k4Closed`. Extends G3 beyond
  the six emit_*fold packs and six AltResidualWitnesses.

  Generated by `backend/proof_complexity/emit_residual_sample_catalog_lean.py`.
  E2 parent: `crossing_residual_catalog_mass.json` (461/461).
-/

import PNPLab.MembershipTransport

namespace PNPLab.Resolution
{"".join(blocks)}
theorem all_sample_topology_set_eq :
    {" ∧ ".join(f"{p}TopologySetEq = true" for p in names)} :=
  ⟨{", ".join(f"{p}TopologySetEq_true" for p in names)}⟩

theorem all_sample_no_empty :
    {" ∧ ".join(f"¬ ([] ∈ {p}RClosed)" for p in names)} :=
  ⟨{", ".join(f"{p}R_no_empty" for p in names)}⟩

def sampleCatalogDoc : String :=
  "reports/discovery/crossing_residual_catalog_mass.json"

end PNPLab.Resolution
"""
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(body, encoding="utf-8")
    print(f"wrote {OUT} samples={len(names)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
