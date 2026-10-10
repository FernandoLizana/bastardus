/-
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

/-! ### c6Crossing line-graph transport -/

def c6Crossing_baseEdgeSym2 : Fin 8 → Sym2 (Fin 6)
  | 0 => s(0, 1)
  | 1 => s(0, 2)
  | 2 => s(0, 5)
  | 3 => s(1, 2)
  | 4 => s(1, 3)
  | 5 => s(2, 3)
  | 6 => s(3, 4)
  | 7 => s(4, 5)

def c6Crossing_edgeIndex (e : Sym2 (Fin 6)) : Fin 8 :=
  if e = s(0, 1) then 0
  else if e = s(0, 2) then 1
  else if e = s(0, 5) then 2
  else if e = s(1, 2) then 3
  else if e = s(1, 3) then 4
  else if e = s(2, 3) then 5
  else if e = s(3, 4) then 6
  else if e = s(4, 5) then 7
  else 0

theorem c6Crossing_baseEdgeSym2_mem (i : Fin 8) :
    c6Crossing_baseEdgeSym2 i ∈ c6CrossingSmokeGraph.edgeSet := by
  fin_cases i <;> native_decide

theorem c6Crossing_edgeIndex_base (i : Fin 8) :
    c6Crossing_edgeIndex (c6Crossing_baseEdgeSym2 i) = i := by
  fin_cases i <;> native_decide

theorem c6Crossing_edgeInRange (e : Sym2 (Fin 6)) :
    e ∈ c6CrossingSmokeGraph.edgeSet ↔ ∃ i, c6Crossing_baseEdgeSym2 i = e := by
  fin_cases e <;> native_decide

theorem c6Crossing_edgeIndex_eq_of_baseEdge (i : Fin 8) (e : Sym2 (Fin 6))
    (h : c6Crossing_baseEdgeSym2 i = e) : c6Crossing_edgeIndex e = i := by
  subst h
  exact c6Crossing_edgeIndex_base i

theorem c6Crossing_edgeIndex_roundtrip (e : Sym2 (Fin 6)) (h : e ∈ c6CrossingSmokeGraph.edgeSet) :
    c6Crossing_baseEdgeSym2 (c6Crossing_edgeIndex e) = e := by
  obtain ⟨i, hi⟩ := (c6Crossing_edgeInRange e).mp h
  rw [c6Crossing_edgeIndex_eq_of_baseEdge i e hi]
  exact hi

def c6Crossing_smokeEdge (i : Fin 8) : c6CrossingSmokeGraph.edgeSet :=
  smokeEdgeOfSym2 (G := c6CrossingSmokeGraph) (c6Crossing_baseEdgeSym2 i) (c6Crossing_baseEdgeSym2_mem i)

def c6Crossing_edgeEquiv : Fin 8 ≃ c6CrossingSmokeGraph.edgeSet where
  toFun := c6Crossing_smokeEdge
  invFun e := c6Crossing_edgeIndex e.val
  left_inv i := by
    dsimp [c6Crossing_smokeEdge, smokeEdgeOfSym2]
    exact c6Crossing_edgeIndex_base i
  right_inv e := by
    apply Subtype.ext
    exact c6Crossing_edgeIndex_roundtrip e.val e.property

theorem c6Crossing_lineGraph_map_eq :
    (c6Crossing_lineGraphFin.map c6Crossing_edgeEquiv) = lineGraph c6CrossingSmokeGraph := by
  apply SimpleGraph.ext
  funext u v
  obtain ⟨i, hi⟩ := c6Crossing_edgeEquiv.surjective u
  obtain ⟨j, hj⟩ := c6Crossing_edgeEquiv.surjective v
  rw [← hi, ← hj]
  simp only [SimpleGraph.map_adj', lineGraph_adj_iff_exists, c6Crossing_lineGraphFin,
    graphOfEdgeList8, graphOfEdgeList8Adj, c6Crossing_lineEdges, c6Crossing_edgeEquiv,
    c6Crossing_smokeEdge, smokeEdgeOfSym2, c6Crossing_baseEdgeSym2, c6CrossingSmokeGraph]
  fin_cases i <;> fin_cases j <;> native_decide

theorem c6Crossing_lineGraph_hasTreeDecomp_4 :
    HasTreeDecomp (lineGraph c6CrossingSmokeGraph) 4 := by
  have hIso := Iso.map c6Crossing_edgeEquiv c6Crossing_lineGraphFin
  have h := hasTreeDecomp_mapIso hIso 4 c6Crossing_fin_hasTreeDecomp_4
  exact hasTreeDecomp_congr c6Crossing_lineGraph_map_eq 4 h

theorem c6CrossingGraph_lineGraph_hasTreeDecomp_4 :
    HasTreeDecomp (lineGraph c6CrossingGraph.toSimpleGraph) 4 :=
  hasTreeDecomp_lineGraph_base_eq (c6CrossingGraph_toSimpleGraph_eq_smoke).symm 4 c6Crossing_lineGraph_hasTreeDecomp_4

/-! ### c7Crossing line-graph transport -/

def c7Crossing_baseEdgeSym2 : Fin 9 → Sym2 (Fin 7)
  | 0 => s(0, 1)
  | 1 => s(0, 2)
  | 2 => s(0, 6)
  | 3 => s(1, 2)
  | 4 => s(1, 3)
  | 5 => s(2, 3)
  | 6 => s(3, 4)
  | 7 => s(4, 5)
  | 8 => s(5, 6)

def c7Crossing_edgeIndex (e : Sym2 (Fin 7)) : Fin 9 :=
  if e = s(0, 1) then 0
  else if e = s(0, 2) then 1
  else if e = s(0, 6) then 2
  else if e = s(1, 2) then 3
  else if e = s(1, 3) then 4
  else if e = s(2, 3) then 5
  else if e = s(3, 4) then 6
  else if e = s(4, 5) then 7
  else if e = s(5, 6) then 8
  else 0

theorem c7Crossing_baseEdgeSym2_mem (i : Fin 9) :
    c7Crossing_baseEdgeSym2 i ∈ c7CrossingSmokeGraph.edgeSet := by
  fin_cases i <;> native_decide

theorem c7Crossing_edgeIndex_base (i : Fin 9) :
    c7Crossing_edgeIndex (c7Crossing_baseEdgeSym2 i) = i := by
  fin_cases i <;> native_decide

theorem c7Crossing_edgeInRange (e : Sym2 (Fin 7)) :
    e ∈ c7CrossingSmokeGraph.edgeSet ↔ ∃ i, c7Crossing_baseEdgeSym2 i = e := by
  fin_cases e <;> native_decide

theorem c7Crossing_edgeIndex_eq_of_baseEdge (i : Fin 9) (e : Sym2 (Fin 7))
    (h : c7Crossing_baseEdgeSym2 i = e) : c7Crossing_edgeIndex e = i := by
  subst h
  exact c7Crossing_edgeIndex_base i

theorem c7Crossing_edgeIndex_roundtrip (e : Sym2 (Fin 7)) (h : e ∈ c7CrossingSmokeGraph.edgeSet) :
    c7Crossing_baseEdgeSym2 (c7Crossing_edgeIndex e) = e := by
  obtain ⟨i, hi⟩ := (c7Crossing_edgeInRange e).mp h
  rw [c7Crossing_edgeIndex_eq_of_baseEdge i e hi]
  exact hi

def c7Crossing_smokeEdge (i : Fin 9) : c7CrossingSmokeGraph.edgeSet :=
  smokeEdgeOfSym2 (G := c7CrossingSmokeGraph) (c7Crossing_baseEdgeSym2 i) (c7Crossing_baseEdgeSym2_mem i)

def c7Crossing_edgeEquiv : Fin 9 ≃ c7CrossingSmokeGraph.edgeSet where
  toFun := c7Crossing_smokeEdge
  invFun e := c7Crossing_edgeIndex e.val
  left_inv i := by
    dsimp [c7Crossing_smokeEdge, smokeEdgeOfSym2]
    exact c7Crossing_edgeIndex_base i
  right_inv e := by
    apply Subtype.ext
    exact c7Crossing_edgeIndex_roundtrip e.val e.property

theorem c7Crossing_lineGraph_map_eq :
    (c7Crossing_lineGraphFin.map c7Crossing_edgeEquiv) = lineGraph c7CrossingSmokeGraph := by
  apply SimpleGraph.ext
  funext u v
  obtain ⟨i, hi⟩ := c7Crossing_edgeEquiv.surjective u
  obtain ⟨j, hj⟩ := c7Crossing_edgeEquiv.surjective v
  rw [← hi, ← hj]
  simp only [SimpleGraph.map_adj', lineGraph_adj_iff_exists, c7Crossing_lineGraphFin,
    graphOfEdgeList9, graphOfEdgeList9Adj, c7Crossing_lineEdges, c7Crossing_edgeEquiv,
    c7Crossing_smokeEdge, smokeEdgeOfSym2, c7Crossing_baseEdgeSym2, c7CrossingSmokeGraph]
  fin_cases i <;> fin_cases j <;> native_decide

theorem c7Crossing_lineGraph_hasTreeDecomp_4 :
    HasTreeDecomp (lineGraph c7CrossingSmokeGraph) 4 := by
  have hIso := Iso.map c7Crossing_edgeEquiv c7Crossing_lineGraphFin
  have h := hasTreeDecomp_mapIso hIso 4 c7Crossing_fin_hasTreeDecomp_4
  exact hasTreeDecomp_congr c7Crossing_lineGraph_map_eq 4 h

theorem c7CrossingGraph_lineGraph_hasTreeDecomp_4 :
    HasTreeDecomp (lineGraph c7CrossingGraph.toSimpleGraph) 4 :=
  hasTreeDecomp_lineGraph_base_eq (c7CrossingGraph_toSimpleGraph_eq_smoke).symm 4 c7Crossing_lineGraph_hasTreeDecomp_4

/-! ### c7Nested line-graph transport -/

def c7Nested_baseEdgeSym2 : Fin 8 → Sym2 (Fin 7)
  | 0 => s(0, 1)
  | 1 => s(0, 3)
  | 2 => s(0, 6)
  | 3 => s(1, 2)
  | 4 => s(2, 3)
  | 5 => s(3, 4)
  | 6 => s(4, 5)
  | 7 => s(5, 6)

def c7Nested_edgeIndex (e : Sym2 (Fin 7)) : Fin 8 :=
  if e = s(0, 1) then 0
  else if e = s(0, 3) then 1
  else if e = s(0, 6) then 2
  else if e = s(1, 2) then 3
  else if e = s(2, 3) then 4
  else if e = s(3, 4) then 5
  else if e = s(4, 5) then 6
  else if e = s(5, 6) then 7
  else 0

theorem c7Nested_baseEdgeSym2_mem (i : Fin 8) :
    c7Nested_baseEdgeSym2 i ∈ c7NestedSmokeGraph.edgeSet := by
  fin_cases i <;> native_decide

theorem c7Nested_edgeIndex_base (i : Fin 8) :
    c7Nested_edgeIndex (c7Nested_baseEdgeSym2 i) = i := by
  fin_cases i <;> native_decide

theorem c7Nested_edgeInRange (e : Sym2 (Fin 7)) :
    e ∈ c7NestedSmokeGraph.edgeSet ↔ ∃ i, c7Nested_baseEdgeSym2 i = e := by
  fin_cases e <;> native_decide

theorem c7Nested_edgeIndex_eq_of_baseEdge (i : Fin 8) (e : Sym2 (Fin 7))
    (h : c7Nested_baseEdgeSym2 i = e) : c7Nested_edgeIndex e = i := by
  subst h
  exact c7Nested_edgeIndex_base i

theorem c7Nested_edgeIndex_roundtrip (e : Sym2 (Fin 7)) (h : e ∈ c7NestedSmokeGraph.edgeSet) :
    c7Nested_baseEdgeSym2 (c7Nested_edgeIndex e) = e := by
  obtain ⟨i, hi⟩ := (c7Nested_edgeInRange e).mp h
  rw [c7Nested_edgeIndex_eq_of_baseEdge i e hi]
  exact hi

def c7Nested_smokeEdge (i : Fin 8) : c7NestedSmokeGraph.edgeSet :=
  smokeEdgeOfSym2 (G := c7NestedSmokeGraph) (c7Nested_baseEdgeSym2 i) (c7Nested_baseEdgeSym2_mem i)

def c7Nested_edgeEquiv : Fin 8 ≃ c7NestedSmokeGraph.edgeSet where
  toFun := c7Nested_smokeEdge
  invFun e := c7Nested_edgeIndex e.val
  left_inv i := by
    dsimp [c7Nested_smokeEdge, smokeEdgeOfSym2]
    exact c7Nested_edgeIndex_base i
  right_inv e := by
    apply Subtype.ext
    exact c7Nested_edgeIndex_roundtrip e.val e.property

theorem c7Nested_lineGraph_map_eq :
    (c7Nested_lineGraphFin.map c7Nested_edgeEquiv) = lineGraph c7NestedSmokeGraph := by
  apply SimpleGraph.ext
  funext u v
  obtain ⟨i, hi⟩ := c7Nested_edgeEquiv.surjective u
  obtain ⟨j, hj⟩ := c7Nested_edgeEquiv.surjective v
  rw [← hi, ← hj]
  simp only [SimpleGraph.map_adj', lineGraph_adj_iff_exists, c7Nested_lineGraphFin,
    graphOfEdgeList8, graphOfEdgeList8Adj, c7Nested_lineEdges, c7Nested_edgeEquiv,
    c7Nested_smokeEdge, smokeEdgeOfSym2, c7Nested_baseEdgeSym2, c7NestedSmokeGraph]
  fin_cases i <;> fin_cases j <;> native_decide

theorem c7Nested_lineGraph_hasTreeDecomp_3 :
    HasTreeDecomp (lineGraph c7NestedSmokeGraph) 3 := by
  have hIso := Iso.map c7Nested_edgeEquiv c7Nested_lineGraphFin
  have h := hasTreeDecomp_mapIso hIso 3 c7Nested_fin_hasTreeDecomp_3
  exact hasTreeDecomp_congr c7Nested_lineGraph_map_eq 3 h

theorem c7NestedGraph_lineGraph_hasTreeDecomp_3 :
    HasTreeDecomp (lineGraph c7NestedGraph.toSimpleGraph) 3 :=
  hasTreeDecomp_lineGraph_base_eq (c7NestedGraph_toSimpleGraph_eq_smoke).symm 3 c7Nested_lineGraph_hasTreeDecomp_3

/-! ### c8Crossing line-graph transport -/

def c8Crossing_baseEdgeSym2 : Fin 10 → Sym2 (Fin 8)
  | 0 => s(0, 1)
  | 1 => s(0, 2)
  | 2 => s(0, 7)
  | 3 => s(1, 2)
  | 4 => s(1, 3)
  | 5 => s(2, 3)
  | 6 => s(3, 4)
  | 7 => s(4, 5)
  | 8 => s(5, 6)
  | 9 => s(6, 7)

def c8Crossing_edgeIndex (e : Sym2 (Fin 8)) : Fin 10 :=
  if e = s(0, 1) then 0
  else if e = s(0, 2) then 1
  else if e = s(0, 7) then 2
  else if e = s(1, 2) then 3
  else if e = s(1, 3) then 4
  else if e = s(2, 3) then 5
  else if e = s(3, 4) then 6
  else if e = s(4, 5) then 7
  else if e = s(5, 6) then 8
  else if e = s(6, 7) then 9
  else 0

theorem c8Crossing_baseEdgeSym2_mem (i : Fin 10) :
    c8Crossing_baseEdgeSym2 i ∈ c8CrossingSmokeGraph.edgeSet := by
  fin_cases i <;> native_decide

theorem c8Crossing_edgeIndex_base (i : Fin 10) :
    c8Crossing_edgeIndex (c8Crossing_baseEdgeSym2 i) = i := by
  fin_cases i <;> native_decide

theorem c8Crossing_edgeInRange (e : Sym2 (Fin 8)) :
    e ∈ c8CrossingSmokeGraph.edgeSet ↔ ∃ i, c8Crossing_baseEdgeSym2 i = e := by
  fin_cases e <;> native_decide

theorem c8Crossing_edgeIndex_eq_of_baseEdge (i : Fin 10) (e : Sym2 (Fin 8))
    (h : c8Crossing_baseEdgeSym2 i = e) : c8Crossing_edgeIndex e = i := by
  subst h
  exact c8Crossing_edgeIndex_base i

theorem c8Crossing_edgeIndex_roundtrip (e : Sym2 (Fin 8)) (h : e ∈ c8CrossingSmokeGraph.edgeSet) :
    c8Crossing_baseEdgeSym2 (c8Crossing_edgeIndex e) = e := by
  obtain ⟨i, hi⟩ := (c8Crossing_edgeInRange e).mp h
  rw [c8Crossing_edgeIndex_eq_of_baseEdge i e hi]
  exact hi

def c8Crossing_smokeEdge (i : Fin 10) : c8CrossingSmokeGraph.edgeSet :=
  smokeEdgeOfSym2 (G := c8CrossingSmokeGraph) (c8Crossing_baseEdgeSym2 i) (c8Crossing_baseEdgeSym2_mem i)

def c8Crossing_edgeEquiv : Fin 10 ≃ c8CrossingSmokeGraph.edgeSet where
  toFun := c8Crossing_smokeEdge
  invFun e := c8Crossing_edgeIndex e.val
  left_inv i := by
    dsimp [c8Crossing_smokeEdge, smokeEdgeOfSym2]
    exact c8Crossing_edgeIndex_base i
  right_inv e := by
    apply Subtype.ext
    exact c8Crossing_edgeIndex_roundtrip e.val e.property

theorem c8Crossing_lineGraph_map_eq :
    (c8Crossing_lineGraphFin.map c8Crossing_edgeEquiv) = lineGraph c8CrossingSmokeGraph := by
  apply SimpleGraph.ext
  funext u v
  obtain ⟨i, hi⟩ := c8Crossing_edgeEquiv.surjective u
  obtain ⟨j, hj⟩ := c8Crossing_edgeEquiv.surjective v
  rw [← hi, ← hj]
  simp only [SimpleGraph.map_adj', lineGraph_adj_iff_exists, c8Crossing_lineGraphFin,
    graphOfEdgeList10, graphOfEdgeList10Adj, c8Crossing_lineEdges, c8Crossing_edgeEquiv,
    c8Crossing_smokeEdge, smokeEdgeOfSym2, c8Crossing_baseEdgeSym2, c8CrossingSmokeGraph]
  fin_cases i <;> fin_cases j <;> native_decide

theorem c8Crossing_lineGraph_hasTreeDecomp_4 :
    HasTreeDecomp (lineGraph c8CrossingSmokeGraph) 4 := by
  have hIso := Iso.map c8Crossing_edgeEquiv c8Crossing_lineGraphFin
  have h := hasTreeDecomp_mapIso hIso 4 c8Crossing_fin_hasTreeDecomp_4
  exact hasTreeDecomp_congr c8Crossing_lineGraph_map_eq 4 h

theorem c8CrossingGraph_lineGraph_hasTreeDecomp_4 :
    HasTreeDecomp (lineGraph c8CrossingGraph.toSimpleGraph) 4 :=
  hasTreeDecomp_lineGraph_base_eq (c8CrossingGraph_toSimpleGraph_eq_smoke).symm 4 c8Crossing_lineGraph_hasTreeDecomp_4

/-! ### c9Crossing line-graph transport -/

def c9Crossing_baseEdgeSym2 : Fin 11 → Sym2 (Fin 9)
  | 0 => s(0, 1)
  | 1 => s(0, 2)
  | 2 => s(0, 8)
  | 3 => s(1, 2)
  | 4 => s(1, 3)
  | 5 => s(2, 3)
  | 6 => s(3, 4)
  | 7 => s(4, 5)
  | 8 => s(5, 6)
  | 9 => s(6, 7)
  | 10 => s(7, 8)

def c9Crossing_edgeIndex (e : Sym2 (Fin 9)) : Fin 11 :=
  if e = s(0, 1) then 0
  else if e = s(0, 2) then 1
  else if e = s(0, 8) then 2
  else if e = s(1, 2) then 3
  else if e = s(1, 3) then 4
  else if e = s(2, 3) then 5
  else if e = s(3, 4) then 6
  else if e = s(4, 5) then 7
  else if e = s(5, 6) then 8
  else if e = s(6, 7) then 9
  else if e = s(7, 8) then 10
  else 0

theorem c9Crossing_baseEdgeSym2_mem (i : Fin 11) :
    c9Crossing_baseEdgeSym2 i ∈ c9CrossingSmokeGraph.edgeSet := by
  fin_cases i <;> native_decide

theorem c9Crossing_edgeIndex_base (i : Fin 11) :
    c9Crossing_edgeIndex (c9Crossing_baseEdgeSym2 i) = i := by
  fin_cases i <;> native_decide

theorem c9Crossing_edgeInRange (e : Sym2 (Fin 9)) :
    e ∈ c9CrossingSmokeGraph.edgeSet ↔ ∃ i, c9Crossing_baseEdgeSym2 i = e := by
  fin_cases e <;> native_decide

theorem c9Crossing_edgeIndex_eq_of_baseEdge (i : Fin 11) (e : Sym2 (Fin 9))
    (h : c9Crossing_baseEdgeSym2 i = e) : c9Crossing_edgeIndex e = i := by
  subst h
  exact c9Crossing_edgeIndex_base i

theorem c9Crossing_edgeIndex_roundtrip (e : Sym2 (Fin 9)) (h : e ∈ c9CrossingSmokeGraph.edgeSet) :
    c9Crossing_baseEdgeSym2 (c9Crossing_edgeIndex e) = e := by
  obtain ⟨i, hi⟩ := (c9Crossing_edgeInRange e).mp h
  rw [c9Crossing_edgeIndex_eq_of_baseEdge i e hi]
  exact hi

def c9Crossing_smokeEdge (i : Fin 11) : c9CrossingSmokeGraph.edgeSet :=
  smokeEdgeOfSym2 (G := c9CrossingSmokeGraph) (c9Crossing_baseEdgeSym2 i) (c9Crossing_baseEdgeSym2_mem i)

def c9Crossing_edgeEquiv : Fin 11 ≃ c9CrossingSmokeGraph.edgeSet where
  toFun := c9Crossing_smokeEdge
  invFun e := c9Crossing_edgeIndex e.val
  left_inv i := by
    dsimp [c9Crossing_smokeEdge, smokeEdgeOfSym2]
    exact c9Crossing_edgeIndex_base i
  right_inv e := by
    apply Subtype.ext
    exact c9Crossing_edgeIndex_roundtrip e.val e.property

theorem c9Crossing_lineGraph_map_eq :
    (c9Crossing_lineGraphFin.map c9Crossing_edgeEquiv) = lineGraph c9CrossingSmokeGraph := by
  apply SimpleGraph.ext
  funext u v
  obtain ⟨i, hi⟩ := c9Crossing_edgeEquiv.surjective u
  obtain ⟨j, hj⟩ := c9Crossing_edgeEquiv.surjective v
  rw [← hi, ← hj]
  simp only [SimpleGraph.map_adj', lineGraph_adj_iff_exists, c9Crossing_lineGraphFin,
    graphOfEdgeList11, graphOfEdgeList11Adj, c9Crossing_lineEdges, c9Crossing_edgeEquiv,
    c9Crossing_smokeEdge, smokeEdgeOfSym2, c9Crossing_baseEdgeSym2, c9CrossingSmokeGraph]
  fin_cases i <;> fin_cases j <;> native_decide

theorem c9Crossing_lineGraph_hasTreeDecomp_4 :
    HasTreeDecomp (lineGraph c9CrossingSmokeGraph) 4 := by
  have hIso := Iso.map c9Crossing_edgeEquiv c9Crossing_lineGraphFin
  have h := hasTreeDecomp_mapIso hIso 4 c9Crossing_fin_hasTreeDecomp_4
  exact hasTreeDecomp_congr c9Crossing_lineGraph_map_eq 4 h

theorem c9CrossingGraph_lineGraph_hasTreeDecomp_4 :
    HasTreeDecomp (lineGraph c9CrossingGraph.toSimpleGraph) 4 :=
  hasTreeDecomp_lineGraph_base_eq (c9CrossingGraph_toSimpleGraph_eq_smoke).symm 4 c9Crossing_lineGraph_hasTreeDecomp_4

/-! ### c9Nested line-graph transport -/

def c9Nested_baseEdgeSym2 : Fin 10 → Sym2 (Fin 9)
  | 0 => s(0, 1)
  | 1 => s(0, 5)
  | 2 => s(0, 8)
  | 3 => s(1, 2)
  | 4 => s(2, 3)
  | 5 => s(3, 4)
  | 6 => s(4, 5)
  | 7 => s(5, 6)
  | 8 => s(6, 7)
  | 9 => s(7, 8)

def c9Nested_edgeIndex (e : Sym2 (Fin 9)) : Fin 10 :=
  if e = s(0, 1) then 0
  else if e = s(0, 5) then 1
  else if e = s(0, 8) then 2
  else if e = s(1, 2) then 3
  else if e = s(2, 3) then 4
  else if e = s(3, 4) then 5
  else if e = s(4, 5) then 6
  else if e = s(5, 6) then 7
  else if e = s(6, 7) then 8
  else if e = s(7, 8) then 9
  else 0

theorem c9Nested_baseEdgeSym2_mem (i : Fin 10) :
    c9Nested_baseEdgeSym2 i ∈ c9NestedSmokeGraph.edgeSet := by
  fin_cases i <;> native_decide

theorem c9Nested_edgeIndex_base (i : Fin 10) :
    c9Nested_edgeIndex (c9Nested_baseEdgeSym2 i) = i := by
  fin_cases i <;> native_decide

theorem c9Nested_edgeInRange (e : Sym2 (Fin 9)) :
    e ∈ c9NestedSmokeGraph.edgeSet ↔ ∃ i, c9Nested_baseEdgeSym2 i = e := by
  fin_cases e <;> native_decide

theorem c9Nested_edgeIndex_eq_of_baseEdge (i : Fin 10) (e : Sym2 (Fin 9))
    (h : c9Nested_baseEdgeSym2 i = e) : c9Nested_edgeIndex e = i := by
  subst h
  exact c9Nested_edgeIndex_base i

theorem c9Nested_edgeIndex_roundtrip (e : Sym2 (Fin 9)) (h : e ∈ c9NestedSmokeGraph.edgeSet) :
    c9Nested_baseEdgeSym2 (c9Nested_edgeIndex e) = e := by
  obtain ⟨i, hi⟩ := (c9Nested_edgeInRange e).mp h
  rw [c9Nested_edgeIndex_eq_of_baseEdge i e hi]
  exact hi

def c9Nested_smokeEdge (i : Fin 10) : c9NestedSmokeGraph.edgeSet :=
  smokeEdgeOfSym2 (G := c9NestedSmokeGraph) (c9Nested_baseEdgeSym2 i) (c9Nested_baseEdgeSym2_mem i)

def c9Nested_edgeEquiv : Fin 10 ≃ c9NestedSmokeGraph.edgeSet where
  toFun := c9Nested_smokeEdge
  invFun e := c9Nested_edgeIndex e.val
  left_inv i := by
    dsimp [c9Nested_smokeEdge, smokeEdgeOfSym2]
    exact c9Nested_edgeIndex_base i
  right_inv e := by
    apply Subtype.ext
    exact c9Nested_edgeIndex_roundtrip e.val e.property

theorem c9Nested_lineGraph_map_eq :
    (c9Nested_lineGraphFin.map c9Nested_edgeEquiv) = lineGraph c9NestedSmokeGraph := by
  apply SimpleGraph.ext
  funext u v
  obtain ⟨i, hi⟩ := c9Nested_edgeEquiv.surjective u
  obtain ⟨j, hj⟩ := c9Nested_edgeEquiv.surjective v
  rw [← hi, ← hj]
  simp only [SimpleGraph.map_adj', lineGraph_adj_iff_exists, c9Nested_lineGraphFin,
    graphOfEdgeList10, graphOfEdgeList10Adj, c9Nested_lineEdges, c9Nested_edgeEquiv,
    c9Nested_smokeEdge, smokeEdgeOfSym2, c9Nested_baseEdgeSym2, c9NestedSmokeGraph]
  fin_cases i <;> fin_cases j <;> native_decide

theorem c9Nested_lineGraph_hasTreeDecomp_3 :
    HasTreeDecomp (lineGraph c9NestedSmokeGraph) 3 := by
  have hIso := Iso.map c9Nested_edgeEquiv c9Nested_lineGraphFin
  have h := hasTreeDecomp_mapIso hIso 3 c9Nested_fin_hasTreeDecomp_3
  exact hasTreeDecomp_congr c9Nested_lineGraph_map_eq 3 h

theorem c9NestedGraph_lineGraph_hasTreeDecomp_3 :
    HasTreeDecomp (lineGraph c9NestedGraph.toSimpleGraph) 3 :=
  hasTreeDecomp_lineGraph_base_eq (c9NestedGraph_toSimpleGraph_eq_smoke).symm 3 c9Nested_lineGraph_hasTreeDecomp_3

/-! ### c10Crossing line-graph transport -/

def c10Crossing_baseEdgeSym2 : Fin 12 → Sym2 (Fin 10)
  | 0 => s(0, 1)
  | 1 => s(0, 2)
  | 2 => s(0, 9)
  | 3 => s(1, 2)
  | 4 => s(1, 3)
  | 5 => s(2, 3)
  | 6 => s(3, 4)
  | 7 => s(4, 5)
  | 8 => s(5, 6)
  | 9 => s(6, 7)
  | 10 => s(7, 8)
  | 11 => s(8, 9)

def c10Crossing_edgeIndex (e : Sym2 (Fin 10)) : Fin 12 :=
  if e = s(0, 1) then 0
  else if e = s(0, 2) then 1
  else if e = s(0, 9) then 2
  else if e = s(1, 2) then 3
  else if e = s(1, 3) then 4
  else if e = s(2, 3) then 5
  else if e = s(3, 4) then 6
  else if e = s(4, 5) then 7
  else if e = s(5, 6) then 8
  else if e = s(6, 7) then 9
  else if e = s(7, 8) then 10
  else if e = s(8, 9) then 11
  else 0

theorem c10Crossing_baseEdgeSym2_mem (i : Fin 12) :
    c10Crossing_baseEdgeSym2 i ∈ c10CrossingSmokeGraph.edgeSet := by
  fin_cases i <;> native_decide

theorem c10Crossing_edgeIndex_base (i : Fin 12) :
    c10Crossing_edgeIndex (c10Crossing_baseEdgeSym2 i) = i := by
  fin_cases i <;> native_decide

theorem c10Crossing_edgeInRange (e : Sym2 (Fin 10)) :
    e ∈ c10CrossingSmokeGraph.edgeSet ↔ ∃ i, c10Crossing_baseEdgeSym2 i = e := by
  fin_cases e <;> native_decide

theorem c10Crossing_edgeIndex_eq_of_baseEdge (i : Fin 12) (e : Sym2 (Fin 10))
    (h : c10Crossing_baseEdgeSym2 i = e) : c10Crossing_edgeIndex e = i := by
  subst h
  exact c10Crossing_edgeIndex_base i

theorem c10Crossing_edgeIndex_roundtrip (e : Sym2 (Fin 10)) (h : e ∈ c10CrossingSmokeGraph.edgeSet) :
    c10Crossing_baseEdgeSym2 (c10Crossing_edgeIndex e) = e := by
  obtain ⟨i, hi⟩ := (c10Crossing_edgeInRange e).mp h
  rw [c10Crossing_edgeIndex_eq_of_baseEdge i e hi]
  exact hi

def c10Crossing_smokeEdge (i : Fin 12) : c10CrossingSmokeGraph.edgeSet :=
  smokeEdgeOfSym2 (G := c10CrossingSmokeGraph) (c10Crossing_baseEdgeSym2 i) (c10Crossing_baseEdgeSym2_mem i)

def c10Crossing_edgeEquiv : Fin 12 ≃ c10CrossingSmokeGraph.edgeSet where
  toFun := c10Crossing_smokeEdge
  invFun e := c10Crossing_edgeIndex e.val
  left_inv i := by
    dsimp [c10Crossing_smokeEdge, smokeEdgeOfSym2]
    exact c10Crossing_edgeIndex_base i
  right_inv e := by
    apply Subtype.ext
    exact c10Crossing_edgeIndex_roundtrip e.val e.property

theorem c10Crossing_lineGraph_map_eq :
    (c10Crossing_lineGraphFin.map c10Crossing_edgeEquiv) = lineGraph c10CrossingSmokeGraph := by
  apply SimpleGraph.ext
  funext u v
  obtain ⟨i, hi⟩ := c10Crossing_edgeEquiv.surjective u
  obtain ⟨j, hj⟩ := c10Crossing_edgeEquiv.surjective v
  rw [← hi, ← hj]
  simp only [SimpleGraph.map_adj', lineGraph_adj_iff_exists, c10Crossing_lineGraphFin,
    graphOfEdgeList12, graphOfEdgeList12Adj, c10Crossing_lineEdges, c10Crossing_edgeEquiv,
    c10Crossing_smokeEdge, smokeEdgeOfSym2, c10Crossing_baseEdgeSym2, c10CrossingSmokeGraph]
  fin_cases i <;> fin_cases j <;> native_decide

theorem c10Crossing_lineGraph_hasTreeDecomp_4 :
    HasTreeDecomp (lineGraph c10CrossingSmokeGraph) 4 := by
  have hIso := Iso.map c10Crossing_edgeEquiv c10Crossing_lineGraphFin
  have h := hasTreeDecomp_mapIso hIso 4 c10Crossing_fin_hasTreeDecomp_4
  exact hasTreeDecomp_congr c10Crossing_lineGraph_map_eq 4 h

theorem c10CrossingGraph_lineGraph_hasTreeDecomp_4 :
    HasTreeDecomp (lineGraph c10CrossingGraph.toSimpleGraph) 4 :=
  hasTreeDecomp_lineGraph_base_eq (c10CrossingGraph_toSimpleGraph_eq_smoke).symm 4 c10Crossing_lineGraph_hasTreeDecomp_4

/-! ### c10Nested line-graph transport -/

def c10Nested_baseEdgeSym2 : Fin 11 → Sym2 (Fin 10)
  | 0 => s(0, 1)
  | 1 => s(0, 3)
  | 2 => s(0, 9)
  | 3 => s(1, 2)
  | 4 => s(2, 3)
  | 5 => s(3, 4)
  | 6 => s(4, 5)
  | 7 => s(5, 6)
  | 8 => s(6, 7)
  | 9 => s(7, 8)
  | 10 => s(8, 9)

def c10Nested_edgeIndex (e : Sym2 (Fin 10)) : Fin 11 :=
  if e = s(0, 1) then 0
  else if e = s(0, 3) then 1
  else if e = s(0, 9) then 2
  else if e = s(1, 2) then 3
  else if e = s(2, 3) then 4
  else if e = s(3, 4) then 5
  else if e = s(4, 5) then 6
  else if e = s(5, 6) then 7
  else if e = s(6, 7) then 8
  else if e = s(7, 8) then 9
  else if e = s(8, 9) then 10
  else 0

theorem c10Nested_baseEdgeSym2_mem (i : Fin 11) :
    c10Nested_baseEdgeSym2 i ∈ c10NestedSmokeGraph.edgeSet := by
  fin_cases i <;> native_decide

theorem c10Nested_edgeIndex_base (i : Fin 11) :
    c10Nested_edgeIndex (c10Nested_baseEdgeSym2 i) = i := by
  fin_cases i <;> native_decide

theorem c10Nested_edgeInRange (e : Sym2 (Fin 10)) :
    e ∈ c10NestedSmokeGraph.edgeSet ↔ ∃ i, c10Nested_baseEdgeSym2 i = e := by
  fin_cases e <;> native_decide

theorem c10Nested_edgeIndex_eq_of_baseEdge (i : Fin 11) (e : Sym2 (Fin 10))
    (h : c10Nested_baseEdgeSym2 i = e) : c10Nested_edgeIndex e = i := by
  subst h
  exact c10Nested_edgeIndex_base i

theorem c10Nested_edgeIndex_roundtrip (e : Sym2 (Fin 10)) (h : e ∈ c10NestedSmokeGraph.edgeSet) :
    c10Nested_baseEdgeSym2 (c10Nested_edgeIndex e) = e := by
  obtain ⟨i, hi⟩ := (c10Nested_edgeInRange e).mp h
  rw [c10Nested_edgeIndex_eq_of_baseEdge i e hi]
  exact hi

def c10Nested_smokeEdge (i : Fin 11) : c10NestedSmokeGraph.edgeSet :=
  smokeEdgeOfSym2 (G := c10NestedSmokeGraph) (c10Nested_baseEdgeSym2 i) (c10Nested_baseEdgeSym2_mem i)

def c10Nested_edgeEquiv : Fin 11 ≃ c10NestedSmokeGraph.edgeSet where
  toFun := c10Nested_smokeEdge
  invFun e := c10Nested_edgeIndex e.val
  left_inv i := by
    dsimp [c10Nested_smokeEdge, smokeEdgeOfSym2]
    exact c10Nested_edgeIndex_base i
  right_inv e := by
    apply Subtype.ext
    exact c10Nested_edgeIndex_roundtrip e.val e.property

theorem c10Nested_lineGraph_map_eq :
    (c10Nested_lineGraphFin.map c10Nested_edgeEquiv) = lineGraph c10NestedSmokeGraph := by
  apply SimpleGraph.ext
  funext u v
  obtain ⟨i, hi⟩ := c10Nested_edgeEquiv.surjective u
  obtain ⟨j, hj⟩ := c10Nested_edgeEquiv.surjective v
  rw [← hi, ← hj]
  simp only [SimpleGraph.map_adj', lineGraph_adj_iff_exists, c10Nested_lineGraphFin,
    graphOfEdgeList11, graphOfEdgeList11Adj, c10Nested_lineEdges, c10Nested_edgeEquiv,
    c10Nested_smokeEdge, smokeEdgeOfSym2, c10Nested_baseEdgeSym2, c10NestedSmokeGraph]
  fin_cases i <;> fin_cases j <;> native_decide

theorem c10Nested_lineGraph_hasTreeDecomp_3 :
    HasTreeDecomp (lineGraph c10NestedSmokeGraph) 3 := by
  have hIso := Iso.map c10Nested_edgeEquiv c10Nested_lineGraphFin
  have h := hasTreeDecomp_mapIso hIso 3 c10Nested_fin_hasTreeDecomp_3
  exact hasTreeDecomp_congr c10Nested_lineGraph_map_eq 3 h

theorem c10NestedGraph_lineGraph_hasTreeDecomp_3 :
    HasTreeDecomp (lineGraph c10NestedGraph.toSimpleGraph) 3 :=
  hasTreeDecomp_lineGraph_base_eq (c10NestedGraph_toSimpleGraph_eq_smoke).symm 3 c10Nested_lineGraph_hasTreeDecomp_3

end SmokeLineGraphCert

end PNPLab.ChordWidth
