/-
  Concrete width closures via derivability, plus a trivial elimination step.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure

namespace PNPLab.Resolution

/-- Derivability at width ≤ w. -/
def derivable (axioms : List Clause) (w : Nat) (C : Clause) : Prop :=
  ∃ d : Derivation axioms C, derWidth d ≤ w

/-- Concrete axioms for complementary units. -/
def unitsAxioms : List Clause := [[(1 : Lit)], [(-1 : Lit)]]

/-- Concrete closure of complementary units at width 1. -/
def unitsClosure : WidthClosure 1 where
  axioms := unitsAxioms
  mem := derivable unitsAxioms 1
  axiom_mem := by
    intro C hC hw
    have hmem : C = [(1 : Lit)] ∨ C = [(-1 : Lit)] := by
      simp [unitsAxioms] at hC
      exact hC
    cases hmem with
    | inl h =>
      subst h
      exact ⟨Derivation.ax 0 (by decide), by native_decide⟩
    | inr h =>
      subst h
      exact ⟨Derivation.ax 1 (by decide), by native_decide⟩
  closed := by
    intro C D R p hC hD hRes hwR
    obtain ⟨dC, hwC⟩ := hC
    obtain ⟨dD, hwD⟩ := hD
    refine ⟨Derivation.res p dC dD hRes, ?_⟩
    simp [derWidth]
    exact Nat.max_le.mpr ⟨hwR, Nat.max_le.mpr ⟨hwC, hwD⟩⟩

theorem unitsClosure_has_empty : unitsClosure.mem [] := by
  obtain ⟨d, hd⟩ := units_derive_empty
  exact ⟨d, hd⟩

/-- Identity elimination step (no variable dropped). -/
def identityElimination (w : Nat) (Φ : WidthClosure w) (V : List Nat) :
    EliminationStep w where
  before := Φ
  after := Φ
  V_after := V
  preserves := by
    intro C hB _
    exact hB

/-- Nonempty elimination chain (identity step on units). -/
def unitsEliminationChain : EliminationChain 1 where
  steps := [identityElimination 1 unitsClosure [1]]

/-- Projection inclusion of a closure into itself. -/
def selfProjection (w : Nat) (Φ : WidthClosure w) (V : List Nat) :
    ProjectionInclusion w where
  gClosure := Φ
  rClosure := Φ
  Vres := V
  holds := by
    intro C hG _
    exact hG

theorem no_empty_self_projection
    {w : Nat} (Φ : WidthClosure w) (V : List Nat)
    (h : ¬ Φ.mem []) :
    ¬ (selfProjection w Φ V).gClosure.mem [] :=
  no_empty_of_projection (selfProjection w Φ V) h

end PNPLab.Resolution
