#!/usr/bin/env python3
"""Emit Lean certificate modules for ChordWidth smoke line graphs (c6–c10, c8Crossing).

Skips c5Ofold and c8Nested (hand-maintained in Certificates.lean / CertificatesLine.lean).

Usage:
  PYTHONPATH=scripts python scripts/emit_lean_tree_decomp_smokes.py
"""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(ROOT / "scripts"))

from treewidth.decomp import line_graph_certificate  # noqa: E402

LEAN_OUT = ROOT / "lean" / "PNPLab" / "ChordWidth" / "TreeDecomp"

# cert export name -> Lean metadata (excluding c5 / c8Nested already done)
SMOKE_LEAN = [
    {
        "cert": "c6Crossing_crossing",
        "prefix": "c6Crossing",
        "smoke_graph": "c6CrossingSmokeGraph",
        "graph": "c6CrossingGraph",
        "graph_eq": "c6CrossingGraph_toSimpleGraph_eq_smoke",
        "base_n": 6,
    },
    {
        "cert": "c7Crossing_crossing",
        "prefix": "c7Crossing",
        "smoke_graph": "c7CrossingSmokeGraph",
        "graph": "c7CrossingGraph",
        "graph_eq": "c7CrossingGraph_toSimpleGraph_eq_smoke",
        "base_n": 7,
    },
    {
        "cert": "c7Nested_noncrossing",
        "prefix": "c7Nested",
        "smoke_graph": "c7NestedSmokeGraph",
        "graph": "c7NestedGraph",
        "graph_eq": "c7NestedGraph_toSimpleGraph_eq_smoke",
        "base_n": 7,
    },
    {
        "cert": "c8Crossing_crossing",
        "prefix": "c8Crossing",
        "smoke_graph": "c8CrossingSmokeGraph",
        "graph": "c8CrossingGraph",
        "graph_eq": "c8CrossingGraph_toSimpleGraph_eq_smoke",
        "base_n": 8,
    },
    {
        "cert": "c9Crossing_crossing",
        "prefix": "c9Crossing",
        "smoke_graph": "c9CrossingSmokeGraph",
        "graph": "c9CrossingGraph",
        "graph_eq": "c9CrossingGraph_toSimpleGraph_eq_smoke",
        "base_n": 9,
    },
    {
        "cert": "c9Nested_noncrossing",
        "prefix": "c9Nested",
        "smoke_graph": "c9NestedSmokeGraph",
        "graph": "c9NestedGraph",
        "graph_eq": "c9NestedGraph_toSimpleGraph_eq_smoke",
        "base_n": 9,
    },
    {
        "cert": "c10Crossing_crossing",
        "prefix": "c10Crossing",
        "smoke_graph": "c10CrossingSmokeGraph",
        "graph": "c10CrossingGraph",
        "graph_eq": "c10CrossingGraph_toSimpleGraph_eq_smoke",
        "base_n": 10,
    },
    {
        "cert": "c10Nested_noncrossing",
        "prefix": "c10Nested",
        "smoke_graph": "c10NestedSmokeGraph",
        "graph": "c10NestedGraph",
        "graph_eq": "c10NestedGraph_toSimpleGraph_eq_smoke",
        "base_n": 10,
    },
]


def lean_list_pairs(pairs: list[list[int]]) -> str:
    inner = ", ".join(f"({a}, {b})" for a, b in pairs)
    return f"[{inner}]"


def lean_list_edges(edges: list[list[int]]) -> str:
    return lean_list_pairs(edges)


def lean_bags(bags: list[list[int]], n: int) -> str:
    lines = []
    for i, bag in enumerate(bags):
        elems = ", ".join(str(x) for x in bag)
        lines.append(f"  | {i} => {{{elems}}}")
    return "\n".join(lines)


def bag_intervals(bags: list[list[int]], n_vertices: int) -> list[tuple[int, int]]:
    out: list[tuple[int, int]] = []
    for x in range(n_vertices):
        idxs = [i for i, b in enumerate(bags) if x in b]
        if not idxs:
            raise RuntimeError(f"vertex {x} not covered by any bag")
        out.append((min(idxs), max(idxs)))
    return out


def base_edge_sym2_lines(base_edges: list[list[int]]) -> str:
    lines = []
    for i, (u, v) in enumerate(base_edges):
        lines.append(f"  | {i} => s({u}, {v})")
    return "\n".join(lines)


def edge_index_lines(base_edges: list[list[int]], prefix: str, base_n: int) -> str:
    lines = []
    for i, (u, v) in enumerate(base_edges):
        cond = f"e = s({u}, {v})"
        lines.append(f"  else if {cond} then {i}")
    default = 0
    chain = f"def {prefix}_edgeIndex (e : Sym2 (Fin {base_n})) : Fin {len(base_edges)} :=\n  if e = s({base_edges[0][0]}, {base_edges[0][1]}) then 0"
    for i in range(1, len(base_edges)):
        u, v = base_edges[i]
        chain += f"\n  else if e = s({u}, {v}) then {i}"
    chain += f"\n  else {default}"
    return chain


def emit_graph_of_edge_list(n: int) -> str:
    if n in (7, 10):
        return f"graphOfEdgeList{n}"
    return f"graphOfEdgeList{n}"


def emit_graph_instances(ns: set[int]) -> str:
    chunks = []
    for n in sorted(ns):
        if n in (7, 10):
            continue
        chunks.append(
            f"""def graphOfEdgeList{n}Adj (edges : List (Nat × Nat)) (i j : Fin {n}) : Prop :=
  i ≠ j ∧ ((i.val, j.val) ∈ edges ∨ (j.val, i.val) ∈ edges)

instance graphOfEdgeList{n}Adj_symmInst (edges : List (Nat × Nat)) :
    Std.Symm (graphOfEdgeList{n}Adj edges) where
  symm := fun _ _ h => by
    rcases h with ⟨hne, h⟩
    exact ⟨hne.symm, by simpa [or_comm] using h⟩

instance graphOfEdgeList{n}Adj_irreflInst (edges : List (Nat × Nat)) :
    Std.Irrefl (graphOfEdgeList{n}Adj edges) where
  irrefl := fun i h => by rcases h with ⟨hne, _⟩; exact hne rfl

def graphOfEdgeList{n} (edges : List (Nat × Nat)) : SimpleGraph (Fin {n}) where
  Adj := graphOfEdgeList{n}Adj edges
  symm := inferInstance
  loopless := inferInstance
"""
        )
    return "\n".join(chunks)


def emit_certificates_smokes() -> str:
    certs = []
    line_ns: set[int] = set()
    for meta in SMOKE_LEAN:
        cert = line_graph_certificate(meta["cert"])
        certs.append((meta, cert))
        line_ns.add(cert.n_vertices)

    header = """/-
  Auto-generated Fin-indexed tree-decomposition certificates (c6–c10, c8Crossing).
  Regenerate: `PYTHONPATH=scripts python scripts/emit_lean_tree_decomp_smokes.py`
-/

import PNPLab.ChordWidth.TreeDecomp.Certificates
import PNPLab.ChordWidth.TreeDecomp.CertPathGraph
import PNPLab.ChordWidth.TreeDecomp.CertPathGraphSmokes

namespace PNPLab.ChordWidth

open SimpleGraph
open TreeDecomp

namespace SmokeLineGraphCert

open SmokeLineGraphCert (bagSupWidth)

"""
    body = emit_graph_instances(line_ns)
    chunks = [header, body]

    for meta, cert in certs:
        p = meta["prefix"]
        n = cert.n_vertices
        tw = cert.treewidth
        gol = emit_graph_of_edge_list(n)
        intervals = bag_intervals(cert.bags, n)
        chunks.append(f"/-! ### {p}: tw = {tw} -/\n")
        chunks.append(f"def {p}_lineEdges : List (Nat × Nat) :=\n  {lean_list_edges(cert.edges)}\n")
        chunks.append(f"def {p}_lineGraphFin : SimpleGraph (Fin {n}) :=\n  {gol} {p}_lineEdges\n")
        chunks.append(f"def {p}_bag : Fin {n} → Finset (Fin {n})\n{lean_bags(cert.bags, n)}\n")
        chunks.append(
            f"""theorem {p}_edgeCover :
    ∀ ⦃a b : Fin {n}⦄, {p}_lineGraphFin.Adj a b →
      ∃ w : Fin {n}, a ∈ {p}_bag w ∧ b ∈ {p}_bag w := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    simp [{p}_lineGraphFin, {gol}, {gol}Adj, {p}_lineEdges, {p}_bag] at h ⊢ <;>
    first | contradiction | decide

theorem {p}_preconnected_bag (x : Fin {n}) (a b : Nat)
    (ha : a < {n}) (hb : b < {n}) (hab : a ≤ b)
    (hset : {{w : Fin {n} | x ∈ {p}_bag w}} = certPathGraphInterval {n} a b) :
    (certPathGraph {n}).induce {{w : Fin {n} | x ∈ {p}_bag w}} |>.Preconnected := by
  rw [hset]
  exact certPathGraph_induce_interval_preconnected {n} a b ha hb hab

noncomputable def {p}_fin_decomp : TreeDecomp {p}_lineGraphFin {n} where
  bag := {p}_bag
  tree := certPathGraph {n}
  isTree := certPathGraph{n}_isTree
  vertexCover := by intro x; fin_cases x <;> native_decide
  edgeCover := {p}_edgeCover
  preconnected_induce_T := by
    intro x
    fin_cases x
"""
        )
        for x, (a, b) in enumerate(intervals):
            chunks.append(
                f"    · exact {p}_preconnected_bag {x} {a} {b} (by decide) (by decide) (by decide)\n"
                f"        (by ext w; fin_cases w <;> simp [certPathGraphInterval, {p}_bag] <;> decide)\n"
            )
        chunks.append(
            f"""theorem {p}_fin_bagSupWidth : bagSupWidth {p}_bag ≤ {tw} := by native_decide

theorem {p}_fin_hasTreeDecomp_{tw} : HasTreeDecomp {p}_lineGraphFin {tw} := by
  refine ⟨{n}, {p}_fin_decomp, ?_⟩
  have hw : {p}_fin_decomp.width = bagSupWidth {p}_bag := by
    dsimp [TreeDecomp.width, {p}_fin_decomp, {p}_bag, bagSupWidth]
    native_decide
  exact hw ▸ {p}_fin_bagSupWidth

"""
        )

    chunks.append(
        'def certificatesSmokesDoc : String :=\n  "Auto-generated HasTreeDecomp for c6–c10 + c8Crossing smokes."\n'
    )
    chunks.append("end SmokeLineGraphCert\n\nend PNPLab.ChordWidth\n")
    return "".join(chunks)


def emit_certificates_line_smokes() -> str:
    header = """/-
  Auto-generated iso transport for smoke line-graph certificates (c6–c10, c8Crossing).
-/

import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Combinatorics.SimpleGraph.Maps
import PNPLab.ChordWidth.BaseCaseTwoChords.CycleTwoChords
import PNPLab.ChordWidth.TreeDecomp.CertificatesLine
import PNPLab.ChordWidth.TreeDecomp.CertificatesSmokes

namespace PNPLab.ChordWidth

open SimpleGraph
open TreeDecomp

namespace SmokeLineGraphCert

"""
    chunks = [header]
    for meta in SMOKE_LEAN:
        cert = line_graph_certificate(meta["cert"])
        p = meta["prefix"]
        base_n = meta["base_n"]
        n = cert.n_vertices
        tw = cert.treewidth
        gol = emit_graph_of_edge_list(n)
        smoke = meta["smoke_graph"]
        graph = meta["graph"]
        graph_eq = meta["graph_eq"]
        base_edges = cert.base_edges

        chunks.append(f"/-! ### {p} line-graph transport -/\n\n")
        chunks.append(f"def {p}_baseEdgeSym2 : Fin {n} → Sym2 (Fin {base_n})\n")
        chunks.append(base_edge_sym2_lines(base_edges) + "\n\n")
        chunks.append(edge_index_lines(base_edges, p, base_n) + "\n\n")
        chunks.append(
            f"""theorem {p}_baseEdgeSym2_mem (i : Fin {n}) :
    {p}_baseEdgeSym2 i ∈ {smoke}.edgeSet := by
  fin_cases i <;> native_decide

theorem {p}_edgeIndex_base (i : Fin {n}) :
    {p}_edgeIndex ({p}_baseEdgeSym2 i) = i := by
  fin_cases i <;> native_decide

theorem {p}_edgeInRange (e : Sym2 (Fin {base_n})) :
    e ∈ {smoke}.edgeSet ↔ ∃ i, {p}_baseEdgeSym2 i = e := by
  fin_cases e <;> native_decide

theorem {p}_edgeIndex_eq_of_baseEdge (i : Fin {n}) (e : Sym2 (Fin {base_n}))
    (h : {p}_baseEdgeSym2 i = e) : {p}_edgeIndex e = i := by
  subst h
  exact {p}_edgeIndex_base i

theorem {p}_edgeIndex_roundtrip (e : Sym2 (Fin {base_n})) (h : e ∈ {smoke}.edgeSet) :
    {p}_baseEdgeSym2 ({p}_edgeIndex e) = e := by
  obtain ⟨i, hi⟩ := ({p}_edgeInRange e).mp h
  rw [{p}_edgeIndex_eq_of_baseEdge i e hi]
  exact hi

def {p}_smokeEdge (i : Fin {n}) : {smoke}.edgeSet :=
  smokeEdgeOfSym2 (G := {smoke}) ({p}_baseEdgeSym2 i) ({p}_baseEdgeSym2_mem i)

def {p}_edgeEquiv : Fin {n} ≃ {smoke}.edgeSet where
  toFun := {p}_smokeEdge
  invFun e := {p}_edgeIndex e.val
  left_inv i := by
    dsimp [{p}_smokeEdge, smokeEdgeOfSym2]
    exact {p}_edgeIndex_base i
  right_inv e := by
    apply Subtype.ext
    exact {p}_edgeIndex_roundtrip e.val e.property

theorem {p}_lineGraph_map_eq :
    ({p}_lineGraphFin.map {p}_edgeEquiv) = lineGraph {smoke} := by
  apply SimpleGraph.ext
  funext u v
  obtain ⟨i, hi⟩ := {p}_edgeEquiv.surjective u
  obtain ⟨j, hj⟩ := {p}_edgeEquiv.surjective v
  rw [← hi, ← hj]
  simp only [SimpleGraph.map_adj', lineGraph_adj_iff_exists, {p}_lineGraphFin,
    {gol}, {gol}Adj, {p}_lineEdges, {p}_edgeEquiv,
    {p}_smokeEdge, smokeEdgeOfSym2, {p}_baseEdgeSym2, {smoke}]
  fin_cases i <;> fin_cases j <;> native_decide

theorem {p}_lineGraph_hasTreeDecomp_{tw} :
    HasTreeDecomp (lineGraph {smoke}) {tw} := by
  have hIso := Iso.map {p}_edgeEquiv {p}_lineGraphFin
  have h := hasTreeDecomp_mapIso hIso {tw} {p}_fin_hasTreeDecomp_{tw}
  exact hasTreeDecomp_congr {p}_lineGraph_map_eq {tw} h

theorem {graph}_lineGraph_hasTreeDecomp_{tw} :
    HasTreeDecomp (lineGraph {graph}.toSimpleGraph) {tw} :=
  hasTreeDecomp_lineGraph_base_eq ({graph_eq}).symm {tw} {p}_lineGraph_hasTreeDecomp_{tw}

"""
        )

    chunks.append("end SmokeLineGraphCert\n\nend PNPLab.ChordWidth\n")
    return "".join(chunks)


def emit_cert_path_graph_theorems(ns: set[int]) -> str:
    chunks = []
    for n in sorted(ns):
        if n in (7, 10):
            continue
        chunks.append(
            f"""theorem certPathGraph{n}_isTree : (certPathGraph {n}).IsTree := by
  classical
  rw [isTree_iff_connected_and_card]
  refine ⟨(certPathGraph_eq_pathGraph {n}).symm ▸ pathGraph_connected {n - 1}, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_edgeSet, Fintype.card_fin]
  native_decide

"""
        )
    return "".join(chunks)


def main() -> int:
    line_ns = {line_graph_certificate(m["cert"]).n_vertices for m in SMOKE_LEAN}
    cert_path_additions = emit_cert_path_graph_theorems(line_ns)

    cert_smokes_path = LEAN_OUT / "CertificatesSmokes.lean"
    cert_line_path = LEAN_OUT / "CertificatesLineSmokes.lean"
    cert_path_path = LEAN_OUT / "CertPathGraphSmokes.lean"

    cert_smokes_path.write_text(emit_certificates_smokes(), encoding="utf-8")
    cert_line_path.write_text(emit_certificates_line_smokes(), encoding="utf-8")
    cert_path_path.write_text(
        f"""/-
  Auto-generated certPathGraph IsTree lemmas for smoke line-graph orders.
-/

import PNPLab.ChordWidth.TreeDecomp.CertPathGraph

namespace PNPLab.ChordWidth

namespace SmokeLineGraphCert

open SimpleGraph

{cert_path_additions}end SmokeLineGraphCert

end PNPLab.ChordWidth
""",
        encoding="utf-8",
    )

    print(f"Wrote {cert_smokes_path.relative_to(ROOT)}")
    print(f"Wrote {cert_line_path.relative_to(ROOT)}")
    print(f"Wrote {cert_path_path.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
