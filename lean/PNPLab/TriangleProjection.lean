/-
  ProjectionInclusion / EliminationStep for the triangle XOR tip fold.

  Residual membership uses `triRPool` (orientations of residual norms + tauts),
  closed under Lean `resolveOriented` at width 2.
-/

import PNPLab.TriangleTip

namespace PNPLab.Resolution

def triRPool : List Clause :=
  [ []
  , [(-3 : Lit)]
  , [(-3 : Lit), (-3 : Lit)]
  , [(-3 : Lit), (-2 : Lit)]
  , [(-2 : Lit), (-3 : Lit)]
  , [(-3 : Lit), (2 : Lit)]
  , [(2 : Lit), (-3 : Lit)]
  , [(-2 : Lit)]
  , [(-2 : Lit), (-2 : Lit)]
  , [(-2 : Lit), (3 : Lit)]
  , [(3 : Lit), (-2 : Lit)]
  , [(2 : Lit)]
  , [(2 : Lit), (2 : Lit)]
  , [(2 : Lit), (3 : Lit)]
  , [(3 : Lit), (2 : Lit)]
  , [(3 : Lit)]
  , [(3 : Lit), (3 : Lit)]
  , [(2 : Lit), (-2 : Lit)]
  , [(-2 : Lit), (2 : Lit)]
  , [(3 : Lit), (-3 : Lit)]
  , [(-3 : Lit), (3 : Lit)]
  ]

theorem triRPool_closed_bool :
    triClosedUnder triRPool 2 triPivots = true := by
  native_decide

def triProjPoolOK : Bool :=
  triGClosed.all fun C =>
    !(supportedOn C triVres) || triRPool.contains C

theorem triProjPoolOK_true : triProjPoolOK = true := by native_decide

theorem tri_mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : triClosedUnder S w pivots = true)
    {C D R : Clause} {p : Lit}
    (hC : C ∈ S) (hD : D ∈ S)
    (hRes : resolveOriented C D p = some R)
    (hw : clauseWidth R ≤ w)
    (hp : p ∈ pivots) :
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
    exact absurd (of_decide_eq_true hwidth) hnotlt

theorem triG_lits_piv :
    (triGClosed.all fun C => C.all fun lit => decide (lit ∈ triPivots)) = true := by
  native_decide

theorem triRPool_lits_piv :
    (triRPool.all fun C => C.all fun lit => decide (lit ∈ triPivots)) = true := by
  native_decide

theorem tri_pivot_G
    {C D R : Clause} {p : Lit}
    (hC : C ∈ triGClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ triPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp triG_lits_piv) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem tri_pivot_R
    {C D R : Clause} {p : Lit}
    (hC : C ∈ triRPool) (hRes : resolveOriented C D p = some R) :
    p ∈ triPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp triRPool_lits_piv) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

def triGClosurePack : WidthClosure 2 where
  axioms := triGAxioms
  mem := fun C => C ∈ triGClosed
  axiom_mem := by
    intro C hC _
    simp only [triGAxioms, List.mem_cons, List.not_mem_nil, or_false] at hC
    simp only [triGClosed, List.mem_cons]
    rcases hC with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  closed := by
    intro C D R p hC hD hRes hw
    exact tri_mem_of_closed triG_closed_bool hC hD hRes hw (tri_pivot_G hC hRes)

def triRClosurePack : WidthClosure 2 where
  axioms := triRAxioms
  mem := fun C => C ∈ triRPool
  axiom_mem := by
    intro C hC _
    simp only [triRAxioms, List.mem_cons, List.not_mem_nil, or_false] at hC
    simp only [triRPool, List.mem_cons]
    rcases hC with rfl | rfl | rfl | rfl <;> simp
  closed := by
    intro C D R p hC hD hRes hw
    exact tri_mem_of_closed triRPool_closed_bool hC hD hRes hw (tri_pivot_R hC hRes)

theorem tri_supported_in_pool
    {C : Clause} (hG : C ∈ triGClosed) (hsup : supportedOn C triVres = true) :
    C ∈ triRPool := by
  have hall := (List.all_eq_true.mp triProjPoolOK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

def triProjection : ProjectionInclusion 2 where
  gClosure := triGClosurePack
  rClosure := triRClosurePack
  Vres := triVres
  holds := fun _ hG hsup => tri_supported_in_pool hG hsup

def triEliminationStep : EliminationStep 2 where
  before := triGClosurePack
  after := triRClosurePack
  V_after := triVres
  preserves := fun _ hB hsup => tri_supported_in_pool hB hsup

def triEliminationChain : EliminationChain 2 where
  steps := [triEliminationStep]
  certDoc := "lean/PNPLab/TriangleProjection.lean"

theorem tri_no_empty_of_projection
    (h : ¬ triRClosurePack.mem []) :
    ¬ triGClosurePack.mem [] :=
  no_empty_of_projection triProjection h

end PNPLab.Resolution
