/-
  Transport Fin-indexed `HasTreeDecomp` certificates to Mathlib `lineGraph` on smoke graphs.

  Python canonical base-edge order matches `scripts/treewidth/decomp.py::_canonical_edges`.
-/

import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Combinatorics.SimpleGraph.Maps
import PNPLab.ChordWidth.BaseCaseTwoChords.CycleTwoChords
import PNPLab.ChordWidth.BaseCaseTwoChords.TwoChordCore
import PNPLab.ChordWidth.TreeDecomp.Certificates

namespace PNPLab.ChordWidth

open SimpleGraph
open TreeDecomp

namespace SmokeLineGraphCert

def smokeEdgeOfSym2 {n : Nat} (G : SimpleGraph (Fin n)) (e : Sym2 (Fin n))
    (h : e ∈ G.edgeSet) : G.edgeSet :=
  ⟨e, h⟩

/-! ### c5 crossing: |E(G)| = 7, tw(L(G)) = 4 -/

def c5Ofold_baseEdgeSym2 : Fin 7 → Sym2 (Fin 5)
  | 0 => s(0, 1)
  | 1 => s(0, 2)
  | 2 => s(0, 4)
  | 3 => s(1, 2)
  | 4 => s(1, 3)
  | 5 => s(2, 3)
  | 6 => s(3, 4)

def c5Ofold_edgeIndex (e : Sym2 (Fin 5)) : Fin 7 :=
  if e = s(0, 1) then 0
  else if e = s(0, 2) then 1
  else if e = s(0, 4) then 2
  else if e = s(1, 2) then 3
  else if e = s(1, 3) then 4
  else if e = s(2, 3) then 5
  else if e = s(3, 4) then 6
  else 0

theorem c5Ofold_baseEdgeSym2_mem (i : Fin 7) :
    c5Ofold_baseEdgeSym2 i ∈ c5SmokeGraph.edgeSet := by
  fin_cases i <;> native_decide

theorem c5Ofold_edgeIndex_base (i : Fin 7) :
    c5Ofold_edgeIndex (c5Ofold_baseEdgeSym2 i) = i := by
  fin_cases i <;> native_decide

theorem c5SmokeGraph_edgeInRange (e : Sym2 (Fin 5)) :
    e ∈ c5SmokeGraph.edgeSet ↔ ∃ i, c5Ofold_baseEdgeSym2 i = e := by
  fin_cases e <;> native_decide

theorem c5Ofold_edgeIndex_eq_of_baseEdge (i : Fin 7) (e : Sym2 (Fin 5))
    (h : c5Ofold_baseEdgeSym2 i = e) : c5Ofold_edgeIndex e = i := by
  subst h
  exact c5Ofold_edgeIndex_base i

theorem c5Ofold_edgeIndex_roundtrip (e : Sym2 (Fin 5)) (h : e ∈ c5SmokeGraph.edgeSet) :
    c5Ofold_baseEdgeSym2 (c5Ofold_edgeIndex e) = e := by
  obtain ⟨i, hi⟩ := (c5SmokeGraph_edgeInRange e).mp h
  rw [c5Ofold_edgeIndex_eq_of_baseEdge i e hi]
  exact hi

def c5Ofold_smokeEdge (i : Fin 7) : c5SmokeGraph.edgeSet :=
  smokeEdgeOfSym2 (G := c5SmokeGraph) (c5Ofold_baseEdgeSym2 i) (c5Ofold_baseEdgeSym2_mem i)

def c5Ofold_edgeEquiv : Fin 7 ≃ c5SmokeGraph.edgeSet where
  toFun := c5Ofold_smokeEdge
  invFun e := c5Ofold_edgeIndex e.val
  left_inv i := by
    dsimp [c5Ofold_smokeEdge, smokeEdgeOfSym2]
    exact c5Ofold_edgeIndex_base i
  right_inv e := by
    apply Subtype.ext
    exact c5Ofold_edgeIndex_roundtrip e.val e.property

theorem c5Ofold_lineGraph_map_eq :
    (c5Ofold_lineGraphFin.map c5Ofold_edgeEquiv) = lineGraph c5SmokeGraph := by
  apply SimpleGraph.ext
  funext u v
  obtain ⟨i, hi⟩ := c5Ofold_edgeEquiv.surjective u
  obtain ⟨j, hj⟩ := c5Ofold_edgeEquiv.surjective v
  rw [← hi, ← hj]
  simp only [SimpleGraph.map_adj', lineGraph_adj_iff_exists, c5Ofold_lineGraphFin,
    graphOfEdgeList7, graphOfEdgeList7Adj, c5Ofold_lineEdges, c5Ofold_edgeEquiv,
    c5Ofold_smokeEdge, smokeEdgeOfSym2, c5Ofold_baseEdgeSym2, c5SmokeGraph]
  fin_cases i <;> fin_cases j <;> native_decide

theorem c5Ofold_lineGraph_hasTreeDecomp_four :
    HasTreeDecomp (lineGraph c5SmokeGraph) 4 := by
  have hIso := Iso.map c5Ofold_edgeEquiv c5Ofold_lineGraphFin
  have h := hasTreeDecomp_mapIso hIso 4 c5Ofold_fin_hasTreeDecomp_four
  exact hasTreeDecomp_congr c5Ofold_lineGraph_map_eq 4 h

theorem c5OfoldGraph_lineGraph_hasTreeDecomp_four :
    HasTreeDecomp (lineGraph c5OfoldGraph.toSimpleGraph) 4 :=
  hasTreeDecomp_lineGraph_base_eq c5Ofold_smokeGraph_eq.symm 4
    c5Ofold_lineGraph_hasTreeDecomp_four

/-! ### c8 nested: |E(G)| = 10, tw(L(G)) = 3 -/

def c8Nested_baseEdgeSym2 : Fin 10 → Sym2 (Fin 8)
  | 0 => s(0, 1)
  | 1 => s(0, 6)
  | 2 => s(0, 7)
  | 3 => s(1, 2)
  | 4 => s(2, 3)
  | 5 => s(2, 4)
  | 6 => s(3, 4)
  | 7 => s(4, 5)
  | 8 => s(5, 6)
  | 9 => s(6, 7)

def c8Nested_edgeIndex (e : Sym2 (Fin 8)) : Fin 10 :=
  if e = s(0, 1) then 0
  else if e = s(0, 6) then 1
  else if e = s(0, 7) then 2
  else if e = s(1, 2) then 3
  else if e = s(2, 3) then 4
  else if e = s(2, 4) then 5
  else if e = s(3, 4) then 6
  else if e = s(4, 5) then 7
  else if e = s(5, 6) then 8
  else if e = s(6, 7) then 9
  else 0

theorem c8Nested_baseEdgeSym2_mem (i : Fin 10) :
    c8Nested_baseEdgeSym2 i ∈ c8SmokeGraph.edgeSet := by
  fin_cases i <;> native_decide

theorem c8Nested_edgeIndex_base (i : Fin 10) :
    c8Nested_edgeIndex (c8Nested_baseEdgeSym2 i) = i := by
  fin_cases i <;> native_decide

theorem c8SmokeGraph_edgeInRange (e : Sym2 (Fin 8)) :
    e ∈ c8SmokeGraph.edgeSet ↔ ∃ i, c8Nested_baseEdgeSym2 i = e := by
  fin_cases e <;> native_decide

theorem c8Nested_edgeIndex_eq_of_baseEdge (i : Fin 10) (e : Sym2 (Fin 8))
    (h : c8Nested_baseEdgeSym2 i = e) : c8Nested_edgeIndex e = i := by
  subst h
  exact c8Nested_edgeIndex_base i

theorem c8Nested_edgeIndex_roundtrip (e : Sym2 (Fin 8)) (h : e ∈ c8SmokeGraph.edgeSet) :
    c8Nested_baseEdgeSym2 (c8Nested_edgeIndex e) = e := by
  obtain ⟨i, hi⟩ := (c8SmokeGraph_edgeInRange e).mp h
  rw [c8Nested_edgeIndex_eq_of_baseEdge i e hi]
  exact hi

def c8Nested_smokeEdge (i : Fin 10) : c8SmokeGraph.edgeSet :=
  smokeEdgeOfSym2 (G := c8SmokeGraph) (c8Nested_baseEdgeSym2 i) (c8Nested_baseEdgeSym2_mem i)

def c8Nested_edgeEquiv : Fin 10 ≃ c8SmokeGraph.edgeSet where
  toFun := c8Nested_smokeEdge
  invFun e := c8Nested_edgeIndex e.val
  left_inv i := by
    dsimp [c8Nested_smokeEdge, smokeEdgeOfSym2]
    exact c8Nested_edgeIndex_base i
  right_inv e := by
    apply Subtype.ext
    exact c8Nested_edgeIndex_roundtrip e.val e.property

theorem c8Nested_lineGraph_map_eq :
    (c8Nested_lineGraphFin.map c8Nested_edgeEquiv) = lineGraph c8SmokeGraph := by
  apply SimpleGraph.ext
  funext u v
  obtain ⟨i, hi⟩ := c8Nested_edgeEquiv.surjective u
  obtain ⟨j, hj⟩ := c8Nested_edgeEquiv.surjective v
  rw [← hi, ← hj]
  simp only [SimpleGraph.map_adj', lineGraph_adj_iff_exists, c8Nested_lineGraphFin,
    graphOfEdgeList10, graphOfEdgeList10Adj, c8Nested_lineEdges, c8Nested_edgeEquiv,
    c8Nested_smokeEdge, smokeEdgeOfSym2, c8Nested_baseEdgeSym2, c8SmokeGraph]
  fin_cases i <;> fin_cases j <;> native_decide

theorem c8Nested_lineGraph_hasTreeDecomp_three :
    HasTreeDecomp (lineGraph c8SmokeGraph) 3 := by
  have hIso := Iso.map c8Nested_edgeEquiv c8Nested_lineGraphFin
  have h := hasTreeDecomp_mapIso hIso 3 c8Nested_fin_hasTreeDecomp_three
  exact hasTreeDecomp_congr c8Nested_lineGraph_map_eq 3 h

theorem c8NestedGraph_lineGraph_hasTreeDecomp_three :
    HasTreeDecomp (lineGraph c8NestedGraph.toSimpleGraph) 3 :=
  hasTreeDecomp_lineGraph_base_eq c8Nested_smokeGraph_eq.symm 3
    c8Nested_lineGraph_hasTreeDecomp_three

def smokeLineGraphCertLineDoc : String :=
  "Iso transport: c5Ofold/c8Nested lineGraph HasTreeDecomp tw=4/3 from Fin certificates."

end SmokeLineGraphCert

end PNPLab.ChordWidth
