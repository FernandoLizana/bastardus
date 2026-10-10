/-
  Two-chord Δ = 3 core classification (Fase 3).

  Structural K₄ / C₄ core predicates + smoke witnesses for c5Ofold / c8Nested.
-/

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Operations
import PNPLab.ChordWidth.BaseCaseTwoChords.DegreeTwoSuppression
import PNPLab.ChordWidth.Treewidth

namespace PNPLab.ChordWidth

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/--
  Structural K₄ core: four branch vertices, all six suppress-edges present.
-/
def SuppressedCore.isK4 [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (c : SuppressedCore V G) : Prop :=
  c.branch.card = 4 ∧
    c.branch_isBranch (G := G) ∧
    (∀ u ∈ c.branch, ∀ w ∈ c.branch, u ≠ w → branchSuppressAdjacent (G := G) u w) ∧
    c.branchEdgeCount (G := G) = 6

/--
  Structural four-cycle core: four branch vertices, suppress-degree 2, four edges.
-/
def SuppressedCore.isFourCycle [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (c : SuppressedCore V G) : Prop :=
  c.branch.card = 4 ∧
    c.branch_isBranch (G := G) ∧
    (∀ (v : V) (hv : v ∈ c.branch), c.branchSuppressDegree (G := G) v hv = 2) ∧
    c.branchEdgeCount (G := G) = 4

structure CrossingCoreIsK4 (g : CycleTwoChordGraph) (hc : g.chordsCross) where
  core : SuppressedCore (Fin g.n) g.toSimpleGraph
  core_eq_suppressed : core = g.suppressedCore
  hasK4Core : SuppressedCore.isK4 (G := g.toSimpleGraph) core

structure NoncrossingCoreIsFourCycle (g : CycleTwoChordGraph) (hnc : ¬ g.chordsCross) where
  core : SuppressedCore (Fin g.n) g.toSimpleGraph
  core_eq_suppressed : core = g.suppressedCore
  hasFourCycleCore : SuppressedCore.isFourCycle (G := g.toSimpleGraph) core

/-! ### Smoke graphs on instance vertex types -/

theorem c5OfoldGraph_n : c5OfoldGraph.n = 5 := rfl
theorem c8NestedGraph_n : c8NestedGraph.n = 8 := rfl

abbrev c5SmokeGraph : SimpleGraph (Fin c5OfoldGraph.n) :=
  cycleGraph c5OfoldGraph.n ⊔
    edge (⟨0, by decide⟩ : Fin c5OfoldGraph.n) ⟨2, by decide⟩ ⊔
    edge (⟨1, by decide⟩ : Fin c5OfoldGraph.n) ⟨3, by decide⟩

abbrev c8SmokeGraph : SimpleGraph (Fin c8NestedGraph.n) :=
  cycleGraph c8NestedGraph.n ⊔
    edge (⟨0, by decide⟩ : Fin c8NestedGraph.n) ⟨6, by decide⟩ ⊔
    edge (⟨2, by decide⟩ : Fin c8NestedGraph.n) ⟨4, by decide⟩

def c5SmokeSuppressedCore : SuppressedCore (Fin c5OfoldGraph.n) c5SmokeGraph :=
  canonicalSuppressedCore (V := Fin c5OfoldGraph.n) (G := c5SmokeGraph)

def c8SmokeSuppressedCore : SuppressedCore (Fin c8NestedGraph.n) c8SmokeGraph :=
  canonicalSuppressedCore (V := Fin c8NestedGraph.n) (G := c8SmokeGraph)

theorem c5SmokeSuppressedCore_branch_card : c5SmokeSuppressedCore.branch.card = 4 := by
  native_decide

theorem c8SmokeSuppressedCore_branch_card : c8SmokeSuppressedCore.branch.card = 4 := by
  native_decide

theorem c5SmokeSuppressedCore_branchEdgeCount_six :
    c5SmokeSuppressedCore.branchEdgeCount (G := c5SmokeGraph) = 6 := by
  native_decide

theorem c8SmokeSuppressedCore_branchEdgeCount_four :
    c8SmokeSuppressedCore.branchEdgeCount (G := c8SmokeGraph) = 4 := by
  native_decide

theorem c5SmokeSuppressedCore_isK4 :
    SuppressedCore.isK4 (G := c5SmokeGraph) c5SmokeSuppressedCore := by
  unfold SuppressedCore.isK4
  refine ⟨c5SmokeSuppressedCore_branch_card, ?_, ?_, c5SmokeSuppressedCore_branchEdgeCount_six⟩
  · intro v hv; exact branchVertex_of_mem c5SmokeGraph hv
  · native_decide

theorem c8SmokeSuppressedCore_isFourCycle :
    SuppressedCore.isFourCycle (G := c8SmokeGraph) c8SmokeSuppressedCore := by
  unfold SuppressedCore.isFourCycle
  refine ⟨c8SmokeSuppressedCore_branch_card, ?_, ?_, c8SmokeSuppressedCore_branchEdgeCount_four⟩
  · intro v hv; exact branchVertex_of_mem c8SmokeGraph hv
  · native_decide

theorem c5Ofold_smokeGraph_eq : c5OfoldGraph.toSimpleGraph = c5SmokeGraph := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  fin_cases u <;> fin_cases v <;>
    simp [c5SmokeGraph, c5OfoldGraph, CycleTwoChordGraph.toSimpleGraph,
      Bicyclic.CrossingEndpoints.toSimpleGraph, Fin.isValue]

theorem c8Nested_smokeGraph_eq : c8NestedGraph.toSimpleGraph = c8SmokeGraph := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  fin_cases u <;> fin_cases v <;>
    simp [c8SmokeGraph, c8NestedGraph, CycleTwoChordGraph.toSimpleGraph,
      CycleTwoChordGraph.toSimpleGraphNoncrossing, CycleTwoChordGraph.chord1,
      CycleTwoChordGraph.chord2, Fin.isValue]

theorem c5Ofold_core_isK4 :
    SuppressedCore.isK4 (G := c5OfoldGraph.toSimpleGraph) c5OfoldGraph.suppressedCore := by
  rw [CycleTwoChordGraph.suppressedCore]
  have hG := c5Ofold_smokeGraph_eq
  have hbranch := branchVertices_eq_of_graph_eq hG
  obtain ⟨h4, hbr, hadj, h6⟩ := c5SmokeSuppressedCore_isK4
  unfold SuppressedCore.isK4 at *
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [canonicalSuppressedCore_branch_eq, hbranch]; exact h4
  · intro v hv
    rw [canonicalSuppressedCore_branch_eq] at hv
    exact branchVertex_of_mem c5OfoldGraph.toSimpleGraph hv
  · intro u hu w hw hne
    rw [canonicalSuppressedCore_branch_eq] at hu hw
    rw [hbranch] at hu hw
    exact (branchSuppressAdjacent_of_graph_eq hG u w).mpr (hadj u hu w hw hne)
  · have hcount :
        SuppressedCore.branchEdgeCount (G := c5OfoldGraph.toSimpleGraph)
            (canonicalSuppressedCore (G := c5OfoldGraph.toSimpleGraph)) =
          SuppressedCore.branchEdgeCount (G := c5SmokeGraph) c5SmokeSuppressedCore := by
      rw [SuppressedCore.branchEdgeCount_eq
          (c := canonicalSuppressedCore (G := c5OfoldGraph.toSimpleGraph))
          (hbranch := canonicalSuppressedCore_branch_eq (G := c5OfoldGraph.toSimpleGraph)),
        SuppressedCore.branchEdgeCount_eq
          (c := c5SmokeSuppressedCore)
          (hbranch := canonicalSuppressedCore_branch_eq (G := c5SmokeGraph)),
        hbranch]
      simp_rw [branchSuppressAdjacent_of_graph_eq hG]
    rw [hcount]
    exact h6

theorem c8Nested_core_isFourCycle :
    SuppressedCore.isFourCycle (G := c8NestedGraph.toSimpleGraph) c8NestedGraph.suppressedCore := by
  rw [CycleTwoChordGraph.suppressedCore]
  have hG := c8Nested_smokeGraph_eq
  have hbranch := branchVertices_eq_of_graph_eq hG
  obtain ⟨h4, hbr, hdeg, h4e⟩ := c8SmokeSuppressedCore_isFourCycle
  unfold SuppressedCore.isFourCycle at *
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [canonicalSuppressedCore_branch_eq, hbranch]; exact h4
  · intro v hv
    rw [canonicalSuppressedCore_branch_eq] at hv
    exact branchVertex_of_mem c8NestedGraph.toSimpleGraph hv
  · intro v hv
    rw [canonicalSuppressedCore_branch_eq] at hv
    rw [hbranch] at hv
    have hdeg' := hdeg v hv
    simp [SuppressedCore.branchSuppressDegree, canonicalSuppressedCore_branch_eq, hbranch,
      branchSuppressAdjacent_of_graph_eq hG]
    exact hdeg'
  · have hcount :
        SuppressedCore.branchEdgeCount (G := c8NestedGraph.toSimpleGraph)
            (canonicalSuppressedCore (G := c8NestedGraph.toSimpleGraph)) =
          SuppressedCore.branchEdgeCount (G := c8SmokeGraph) c8SmokeSuppressedCore := by
      rw [SuppressedCore.branchEdgeCount_eq
          (c := canonicalSuppressedCore (G := c8NestedGraph.toSimpleGraph))
          (hbranch := canonicalSuppressedCore_branch_eq (G := c8NestedGraph.toSimpleGraph)),
        SuppressedCore.branchEdgeCount_eq
          (c := c8SmokeSuppressedCore)
          (hbranch := canonicalSuppressedCore_branch_eq (G := c8SmokeGraph)),
        hbranch]
      simp_rw [branchSuppressAdjacent_of_graph_eq hG]
    rw [hcount]
    exact h4e

noncomputable def c5Ofold_crossing_core_k4 : CrossingCoreIsK4 c5OfoldGraph c5OfoldGraph_chordsCross :=
  { core := c5OfoldGraph.suppressedCore
    core_eq_suppressed := rfl
    hasK4Core := c5Ofold_core_isK4 }

noncomputable def c8Nested_noncrossing_core :
    NoncrossingCoreIsFourCycle c8NestedGraph c8NestedGraph_not_crossing :=
  { core := c8NestedGraph.suppressedCore
    core_eq_suppressed := rfl
    hasFourCycleCore := c8Nested_core_isFourCycle }

structure CrossingLineGraphTw (g : CycleTwoChordGraph) (hc : g.chordsCross) (k : Nat) where
  tw_exp : LineGraphTreewidthExperimental (Fin g.n) g.toSimpleGraph k
  expected_width : k = 3 ∨ k = 4

structure NoncrossingLineGraphTw (g : CycleTwoChordGraph) (hnc : ¬ g.chordsCross) (k : Nat) where
  tw_exp : LineGraphTreewidthExperimental (Fin g.n) g.toSimpleGraph k
  expected_width : k ≤ 3

def twoChordCoreDoc : String :=
  "CrossingCoreIsK4 / NoncrossingCoreIsFourCycle; c5 K₄ + c8 C₄ smoke; no full SimpleGraph.Iso yet"

def twoChordCoreGapDoc : String :=
  "Remaining: Iso to completeGraph (Fin 4) / cycleGraph 4; universal ∀n core theorems"

end PNPLab.ChordWidth
