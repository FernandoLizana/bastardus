/-
  Tree-peel sketch for outerplanar upper bounds (Category C / G6).

  Mirrors Python `peel_trees`: drop pending degree-1 leaves until the 2-core.
  Sketch-level only (pendingLeaves counter + core); not a Mathlib graph.

  After peel, the residual is an `OuterplanarCoreResidual` (cycle or ear).
-/

import PNPLab.OuterplanarCoreResidual

namespace PNPLab.Outerplanar

/-- Pre-core graph with pending tree leaves (sketch). -/
structure PeelSketch where
  coreVertices : Nat
  pendingLeaves : Nat
  core : OuterplanarCoreResidual

def PeelSketch.totalVertices (p : PeelSketch) : Nat :=
  p.coreVertices + p.pendingLeaves

/-- One peel step: drop a pending leaf. -/
def PeelSketch.peelOne (p : PeelSketch) : PeelSketch where
  coreVertices := p.coreVertices
  pendingLeaves := p.pendingLeaves - 1
  core := p.core

theorem PeelSketch.peelOne_drops (p : PeelSketch) (h : 0 < p.pendingLeaves) :
    (p.peelOne).totalVertices < p.totalVertices := by
  simp [PeelSketch.peelOne, PeelSketch.totalVertices]
  exact Nat.sub_lt h Nat.zero_lt_one

/-- Fuel-bounded peel (exactly `n` leaf drops). -/
def PeelSketch.peelFuel : Nat → PeelSketch → PeelSketch
  | 0, p => p
  | n + 1, p => PeelSketch.peelFuel n p.peelOne

def PeelSketch.peelAll (p : PeelSketch) : PeelSketch :=
  p.peelFuel p.pendingLeaves

theorem PeelSketch.peelFuel_leaves (p : PeelSketch) (n : Nat) :
    (p.peelFuel n).pendingLeaves = p.pendingLeaves - n := by
  induction n generalizing p with
  | zero =>
    simp [PeelSketch.peelFuel]
  | succ n ih =>
    change (p.peelOne.peelFuel n).pendingLeaves = p.pendingLeaves - (n + 1)
    rw [ih p.peelOne, PeelSketch.peelOne]
    rw [Nat.sub_sub, Nat.add_comm]

theorem PeelSketch.peelAll_no_leaves (p : PeelSketch) :
    (p.peelAll).pendingLeaves = 0 := by
  simp [PeelSketch.peelAll, PeelSketch.peelFuel_leaves]

theorem PeelSketch.peelFuel_core (p : PeelSketch) (n : Nat) :
    (p.peelFuel n).core = p.core := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    change (p.peelOne.peelFuel n).core = p.core
    rw [ih p.peelOne]
    rfl

theorem PeelSketch.peelAll_core_eq (p : PeelSketch) :
    (p.peelAll).core = p.core :=
  p.peelFuel_core p.pendingLeaves

/-- After peel: either cycle or an ear exists on the core. -/
theorem PeelSketch.peelAll_earExists (p : PeelSketch) :
    (p.peelAll).core.isCycle = true ∨ (p.peelAll).core.ear.isSome = true := by
  rw [p.peelAll_core_eq]
  exact p.core.earExists

/-- Concrete: pending trees on a C₄ triangle-ear core. -/
def peelC4WithTrees : PeelSketch where
  coreVertices := 4
  pendingLeaves := 3
  core := coreC4Triangle

theorem peelC4WithTrees_done :
    (peelC4WithTrees.peelAll).pendingLeaves = 0 ∧
      (peelC4WithTrees.peelAll).core = coreC4Triangle :=
  ⟨peelC4WithTrees.peelAll_no_leaves, peelC4WithTrees.peelAll_core_eq⟩

/-- After peel, tip fold is available on the (unchanged) C₄ triangle core. -/
theorem peelC4_upper_ready :
    (peelC4WithTrees.peelAll).core = coreC4Triangle ∧
      ∃ tip : EarTipKind,
        ((coreC4Triangle.toSketchOfEar earPathTriangle rfl
            ⟨by decide, Or.inl rfl⟩).classify).tipKind = some tip :=
  ⟨peelC4WithTrees.peelAll_core_eq, coreC4Triangle_tip⟩

def peelDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/TERMINATION.md"

def earMassDocPeel : String :=
  "reports/discovery/outerplanar_ear_existence_mass_n14.json"

end PNPLab.Outerplanar
