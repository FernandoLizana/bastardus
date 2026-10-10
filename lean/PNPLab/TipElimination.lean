/-
  Concrete tip-elimination (toy path-fold step), not an identity step.

  Tip edge var = 1, residual edge var = 2.
    G:  [1], [-1,2], [-2]
    R:  [2], [-2]
  Explicit finite width-2 closures (includes unit [-1] from [-1,2]⊕[-2]);
  projection inclusion on V={2}.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure

namespace PNPLab.Resolution

def tipGAxioms : List Clause :=
  [[(1 : Lit)], [(-1 : Lit), (2 : Lit)], [(-2 : Lit)]]

def tipRAxioms : List Clause :=
  [[(2 : Lit)], [(-2 : Lit)]]

/-- Saturated under width-2 oriented resolve (includes [-1] = strip of [-1,2]⊕[-2]). -/
def tipGClosed : List Clause :=
  [[(1 : Lit)], [(-1 : Lit), (2 : Lit)], [(-2 : Lit)], [(2 : Lit)], [(-1 : Lit)], []]

def tipRClosed : List Clause :=
  [[(2 : Lit)], [(-2 : Lit)], []]

def tipPivots : List Lit := [-4, -3, -2, -1, 0, 1, 2, 3, 4]

def closedUnderResolveRange (S : List Clause) (w : Nat) : Bool :=
  tipPivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem tipG_closed_bool : closedUnderResolveRange tipGClosed 2 = true := by
  native_decide

theorem tipR_closed_bool : closedUnderResolveRange tipRClosed 2 = true := by
  native_decide

theorem tipG_lit_bound
    {C : Clause} (hC : C ∈ tipGClosed) {p : Lit} (hp : p ∈ C) :
    p = -2 ∨ p = -1 ∨ p = 1 ∨ p = 2 := by
  simp only [tipGClosed, List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    exact Or.inr (Or.inr (Or.inl hp))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with hp | hp
    · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr (Or.inr hp))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    exact Or.inl hp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    exact Or.inr (Or.inr (Or.inr hp))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    exact Or.inr (Or.inl hp)
  · cases hp

theorem tipR_lit_bound
    {C : Clause} (hC : C ∈ tipRClosed) {p : Lit} (hp : p ∈ C) :
    p = -2 ∨ p = 2 := by
  simp only [tipRClosed, List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl | rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    exact Or.inr hp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    exact Or.inl hp
  · cases hp

theorem pivot_mem_tipPivots {p : Lit}
    (h : p = -2 ∨ p = -1 ∨ p = 1 ∨ p = 2) : p ∈ tipPivots := by
  simp only [tipPivots, List.mem_cons, List.not_mem_nil, or_false]
  rcases h with rfl | rfl | rfl | rfl <;> decide

theorem tipG_pivot_in_range
    {C D R : Clause} {p : Lit}
    (hC : C ∈ tipGClosed)
    (hRes : resolveOriented C D p = some R) :
    p ∈ tipPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  exact pivot_mem_tipPivots (tipG_lit_bound hC hpC)

theorem tipR_pivot_in_range
    {C D R : Clause} {p : Lit}
    (hC : C ∈ tipRClosed)
    (hRes : resolveOriented C D p = some R) :
    p ∈ tipPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hb := tipR_lit_bound hC hpC
  apply pivot_mem_tipPivots
  rcases hb with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inr rfl))
theorem mem_of_closedUnder
    {S : List Clause} {w : Nat}
    (hbool : closedUnderResolveRange S w = true)
    {C D R : Clause} {p : Lit}
    (hC : C ∈ S) (hD : D ∈ S)
    (hRes : resolveOriented C D p = some R)
    (hw : clauseWidth R ≤ w)
    (hp : p ∈ tipPivots) :
    R ∈ S := by
  have hpall := (List.all_eq_true.mp hbool) p hp
  have hCall := (List.all_eq_true.mp hpall) C hC
  have hDall := (List.all_eq_true.mp hCall) D hD
  simp only [hRes] at hDall
  have hnotlt : ¬ w < clauseWidth R := Nat.not_lt.mpr hw
  cases hwidth : decide (w < clauseWidth R) with
  | false =>
    simp only [hwidth, Bool.false_or] at hDall
    exact (List.contains_iff_mem).mp hDall
  | true =>
    have : w < clauseWidth R := of_decide_eq_true hwidth
    exact absurd this hnotlt

def tipGClosure : WidthClosure 2 where
  axioms := tipGAxioms
  mem := fun C => C ∈ tipGClosed
  axiom_mem := by
    intro C hC _
    simp only [tipGAxioms, List.mem_cons, List.not_mem_nil, or_false] at hC
    simp only [tipGClosed, List.mem_cons]
    rcases hC with rfl | rfl | rfl <;> simp
  closed := by
    intro C D R p hC hD hRes hw
    exact mem_of_closedUnder tipG_closed_bool hC hD hRes hw
      (tipG_pivot_in_range hC hRes)

def tipRClosure : WidthClosure 2 where
  axioms := tipRAxioms
  mem := fun C => C ∈ tipRClosed
  axiom_mem := by
    intro C hC _
    simp only [tipRAxioms, List.mem_cons, List.not_mem_nil, or_false] at hC
    simp only [tipRClosed, List.mem_cons]
    rcases hC with rfl | rfl <;> simp
  closed := by
    intro C D R p hC hD hRes hw
    exact mem_of_closedUnder tipR_closed_bool hC hD hRes hw
      (tipR_pivot_in_range hC hRes)

def tipVres : List Nat := [2]

theorem tip_supported_mem
    {C : Clause} (hG : C ∈ tipGClosed) (hsup : supportedOn C tipVres = true) :
    C ∈ tipRClosed := by
  simp only [tipGClosed, List.mem_cons, List.not_mem_nil, or_false] at hG
  rcases hG with rfl | rfl | rfl | rfl | rfl | rfl
  · simp [supportedOn, tipVres, clauseVars] at hsup
  · simp [supportedOn, tipVres, clauseVars] at hsup
  · simp [tipRClosed]
  · simp [tipRClosed]
  · -- [-1] not supported on {2}
    simp [supportedOn, tipVres, clauseVars] at hsup
  · simp [tipRClosed]

def tipProjection : ProjectionInclusion 2 where
  gClosure := tipGClosure
  rClosure := tipRClosure
  Vres := tipVres
  holds := fun _ hG hsup => tip_supported_mem hG hsup

def tipEliminationStep : EliminationStep 2 where
  before := tipGClosure
  after := tipRClosure
  V_after := tipVres
  preserves := fun _ hB hsup => tip_supported_mem hB hsup

def tipEliminationChain : EliminationChain 2 where
  steps := [tipEliminationStep]
  certDoc := "lean/PNPLab/TipElimination.lean"

theorem tip_unit_resolve :
    resolveOriented ([(1 : Lit)] : Clause) ([(-1 : Lit), (2 : Lit)] : Clause) (1 : Lit)
      = some [(2 : Lit)] := by
  native_decide

theorem tip_empty_resolve :
    resolveOriented ([(2 : Lit)] : Clause) ([(-2 : Lit)] : Clause) (2 : Lit)
      = some ([] : Clause) := by
  native_decide

theorem tipG_has_empty : tipGClosure.mem [] := by
  simp [tipGClosure, tipGClosed]

theorem tipR_has_empty : tipRClosure.mem [] := by
  simp [tipRClosure, tipRClosed]

end PNPLab.Resolution
