/-
  Two-arc path-fold projection chain (n=6 crossing).

  Instance: C_6 + chords (0,3),(2,5). Open arcs fold tip-by-tip:
    G0 Closure₃ size 68
    → G1 Closure₃ size 42
    → R  Closure₃ size 16 (residual K₄ XOR axioms).

  Each hop is a ProjectionInclusion / EliminationStep; the chain is the
  first multi-arc EliminationChain instance in the lab.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures

namespace PNPLab.Resolution

def mfG0Axioms : List Clause :=
  [ [(-8 : Lit), (7 : Lit)]
  , [(-7 : Lit), (8 : Lit)]
  , [(-4 : Lit), (1 : Lit)]
  , [(-1 : Lit), (4 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-3 : Lit)]
  , [(-8 : Lit), (3 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (-2 : Lit)]
  , [(-7 : Lit), (2 : Lit), (5 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-4 : Lit)]
  , [(-6 : Lit), (3 : Lit), (8 : Lit)]
  , [(-6 : Lit), (4 : Lit), (5 : Lit)]
  , [(-5 : Lit), (2 : Lit), (7 : Lit)]
  , [(-5 : Lit), (4 : Lit), (6 : Lit)]
  , [(-4 : Lit), (5 : Lit), (6 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (6 : Lit), (8 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (5 : Lit), (7 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def mfG0Closed : List Clause :=
  [ [(-8 : Lit), (7 : Lit)]
  , [(-7 : Lit), (8 : Lit)]
  , [(-4 : Lit), (1 : Lit)]
  , [(-1 : Lit), (4 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-3 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (2 : Lit), (5 : Lit)]
  , [(-8 : Lit), (2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (3 : Lit), (6 : Lit)]
  , [(-8 : Lit), (3 : Lit), (7 : Lit)]
  , [(-8 : Lit), (5 : Lit), (7 : Lit)]
  , [(-8 : Lit), (6 : Lit), (7 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-3 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (-2 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (2 : Lit), (5 : Lit)]
  , [(-7 : Lit), (2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (3 : Lit), (6 : Lit)]
  , [(-7 : Lit), (3 : Lit), (8 : Lit)]
  , [(-7 : Lit), (5 : Lit), (8 : Lit)]
  , [(-7 : Lit), (6 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-4 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (1 : Lit)]
  , [(-6 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-6 : Lit), (1 : Lit), (5 : Lit)]
  , [(-6 : Lit), (3 : Lit), (7 : Lit)]
  , [(-6 : Lit), (3 : Lit), (8 : Lit)]
  , [(-6 : Lit), (4 : Lit), (5 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (1 : Lit)]
  , [(-5 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (2 : Lit), (7 : Lit)]
  , [(-5 : Lit), (2 : Lit), (8 : Lit)]
  , [(-5 : Lit), (4 : Lit), (6 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (1 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (2 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-4 : Lit), (1 : Lit), (2 : Lit)]
  , [(-4 : Lit), (1 : Lit), (3 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (1 : Lit), (6 : Lit)]
  , [(-4 : Lit), (5 : Lit), (6 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-3 : Lit), (6 : Lit), (7 : Lit)]
  , [(-3 : Lit), (6 : Lit), (8 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-2 : Lit), (5 : Lit), (7 : Lit)]
  , [(-2 : Lit), (5 : Lit), (8 : Lit)]
  , [(-1 : Lit), (2 : Lit), (4 : Lit)]
  , [(-1 : Lit), (3 : Lit), (4 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(-1 : Lit), (4 : Lit), (6 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(2 : Lit), (3 : Lit), (4 : Lit)]
  ]

def mfG1Axioms : List Clause :=
  [ [(-8 : Lit), (7 : Lit)]
  , [(-7 : Lit), (8 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-3 : Lit)]
  , [(-8 : Lit), (3 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (-2 : Lit)]
  , [(-7 : Lit), (2 : Lit), (5 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-4 : Lit)]
  , [(-6 : Lit), (3 : Lit), (8 : Lit)]
  , [(-6 : Lit), (4 : Lit), (5 : Lit)]
  , [(-5 : Lit), (2 : Lit), (7 : Lit)]
  , [(-5 : Lit), (4 : Lit), (6 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (2 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-4 : Lit), (5 : Lit), (6 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-3 : Lit), (6 : Lit), (8 : Lit)]
  , [(-2 : Lit), (5 : Lit), (7 : Lit)]
  , [(2 : Lit), (3 : Lit), (4 : Lit)]
  ]

def mfG1Closed : List Clause :=
  [ [(-8 : Lit), (7 : Lit)]
  , [(-7 : Lit), (8 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-3 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (2 : Lit), (5 : Lit)]
  , [(-8 : Lit), (2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (3 : Lit), (6 : Lit)]
  , [(-8 : Lit), (3 : Lit), (7 : Lit)]
  , [(-8 : Lit), (5 : Lit), (7 : Lit)]
  , [(-8 : Lit), (6 : Lit), (7 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-3 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (-2 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (2 : Lit), (5 : Lit)]
  , [(-7 : Lit), (2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (3 : Lit), (6 : Lit)]
  , [(-7 : Lit), (3 : Lit), (8 : Lit)]
  , [(-7 : Lit), (5 : Lit), (8 : Lit)]
  , [(-7 : Lit), (6 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-4 : Lit)]
  , [(-6 : Lit), (3 : Lit), (7 : Lit)]
  , [(-6 : Lit), (3 : Lit), (8 : Lit)]
  , [(-6 : Lit), (4 : Lit), (5 : Lit)]
  , [(-5 : Lit), (2 : Lit), (7 : Lit)]
  , [(-5 : Lit), (2 : Lit), (8 : Lit)]
  , [(-5 : Lit), (4 : Lit), (6 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (2 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-4 : Lit), (5 : Lit), (6 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-3 : Lit), (6 : Lit), (7 : Lit)]
  , [(-3 : Lit), (6 : Lit), (8 : Lit)]
  , [(-2 : Lit), (5 : Lit), (7 : Lit)]
  , [(-2 : Lit), (5 : Lit), (8 : Lit)]
  , [(2 : Lit), (3 : Lit), (4 : Lit)]
  ]

def mfRAxioms : List Clause :=
  [ [(-8 : Lit), (-6 : Lit), (-3 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (2 : Lit), (5 : Lit)]
  , [(-8 : Lit), (3 : Lit), (6 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-4 : Lit)]
  , [(-6 : Lit), (3 : Lit), (8 : Lit)]
  , [(-6 : Lit), (4 : Lit), (5 : Lit)]
  , [(-5 : Lit), (2 : Lit), (8 : Lit)]
  , [(-5 : Lit), (4 : Lit), (6 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (2 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-4 : Lit), (5 : Lit), (6 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-3 : Lit), (6 : Lit), (8 : Lit)]
  , [(-2 : Lit), (5 : Lit), (8 : Lit)]
  , [(2 : Lit), (3 : Lit), (4 : Lit)]
  ]

abbrev mfRClosed : List Clause := mfRAxioms

def mfPivots : List Lit := [-9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

def mfV1 : List Nat := [2, 3, 4, 5, 6, 7, 8]

def mfVres : List Nat := [2, 3, 4, 5, 6, 8]

def mfClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem mf_mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : mfClosedUnder S w pivots = true)
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

theorem mfG0_closed_bool : mfClosedUnder mfG0Closed 3 mfPivots = true := by
  native_decide

theorem mfG0_lits_in_pivots :
    (mfG0Closed.all fun C => C.all fun lit => decide (lit ∈ mfPivots)) = true := by
  native_decide

theorem mfG0_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ mfG0Closed) (hRes : resolveOriented C D p = some R) :
    p ∈ mfPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp mfG0_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

def mfG0Closure : WidthClosure 3 where
  axioms := mfG0Axioms
  mem := fun C => C ∈ mfG0Closed
  axiom_mem := by
    intro C hC _
    have h : (mfG0Axioms.all fun A => mfG0Closed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact mf_mem_of_closed mfG0_closed_bool hC hD hRes hw (mfG0_pivot hC hRes)

theorem mfG0_no_empty : ¬ mfG0Closure.mem [] := by
  simp [mfG0Closure]
  native_decide


theorem mfG1_closed_bool : mfClosedUnder mfG1Closed 3 mfPivots = true := by
  native_decide

theorem mfG1_lits_in_pivots :
    (mfG1Closed.all fun C => C.all fun lit => decide (lit ∈ mfPivots)) = true := by
  native_decide

theorem mfG1_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ mfG1Closed) (hRes : resolveOriented C D p = some R) :
    p ∈ mfPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp mfG1_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

def mfG1Closure : WidthClosure 3 where
  axioms := mfG1Axioms
  mem := fun C => C ∈ mfG1Closed
  axiom_mem := by
    intro C hC _
    have h : (mfG1Axioms.all fun A => mfG1Closed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact mf_mem_of_closed mfG1_closed_bool hC hD hRes hw (mfG1_pivot hC hRes)

theorem mfG1_no_empty : ¬ mfG1Closure.mem [] := by
  simp [mfG1Closure]
  native_decide


theorem mfR_closed_bool : mfClosedUnder mfRClosed 3 mfPivots = true := by
  native_decide

theorem mfR_lits_in_pivots :
    (mfRClosed.all fun C => C.all fun lit => decide (lit ∈ mfPivots)) = true := by
  native_decide

theorem mfR_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ mfRClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ mfPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp mfR_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

def mfRClosure : WidthClosure 3 where
  axioms := mfRAxioms
  mem := fun C => C ∈ mfRClosed
  axiom_mem := by
    intro C hC _
    have h : (mfRAxioms.all fun A => mfRClosed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact mf_mem_of_closed mfR_closed_bool hC hD hRes hw (mfR_pivot hC hRes)

theorem mfR_no_empty : ¬ mfRClosure.mem [] := by
  simp [mfRClosure]
  native_decide


def mfProj01OK : Bool :=
  mfG0Closed.all fun C =>
    !(supportedOn C mfV1) || mfG1Closed.contains C

def mfProj1ROK : Bool :=
  mfG1Closed.all fun C =>
    !(supportedOn C mfVres) || mfRClosed.contains C

def mfProj0ROK : Bool :=
  mfG0Closed.all fun C =>
    !(supportedOn C mfVres) || mfRClosed.contains C

theorem mfProj01OK_true : mfProj01OK = true := by native_decide
theorem mfProj1ROK_true : mfProj1ROK = true := by native_decide
theorem mfProj0ROK_true : mfProj0ROK = true := by native_decide

theorem mf_supported_01
    {C : Clause} (hG : C ∈ mfG0Closed) (hsup : supportedOn C mfV1 = true) :
    C ∈ mfG1Closed := by
  have hall := (List.all_eq_true.mp mfProj01OK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

theorem mf_supported_1R
    {C : Clause} (hG : C ∈ mfG1Closed) (hsup : supportedOn C mfVres = true) :
    C ∈ mfRClosed := by
  have hall := (List.all_eq_true.mp mfProj1ROK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

theorem mf_supported_0R
    {C : Clause} (hG : C ∈ mfG0Closed) (hsup : supportedOn C mfVres = true) :
    C ∈ mfRClosed := by
  have hall := (List.all_eq_true.mp mfProj0ROK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

def mfStep01 : EliminationStep 3 where
  before := mfG0Closure
  after := mfG1Closure
  V_after := mfV1
  preserves := fun _ hB hsup => mf_supported_01 hB hsup

def mfStep1R : EliminationStep 3 where
  before := mfG1Closure
  after := mfRClosure
  V_after := mfVres
  preserves := fun _ hB hsup => mf_supported_1R hB hsup

def mfEliminationChain : EliminationChain 3 where
  steps := [mfStep01, mfStep1R]
  certDoc := "lean/PNPLab/MultiFoldProjection.lean"

theorem mfNest : varsSubset mfVres mfV1 = true := by native_decide

theorem mfLink1R : StepLink 3 mfStep01 mfStep1R where
  bridge := rfl
  nest := mfNest

def mfLinked : LinkedChain 3 [mfStep01, mfStep1R] :=
  linkedChainCons mfLink1R (LinkedChain.singleton mfStep1R)

/-- G0 → R via generic `projectionOfLinkedChain` (StepLink / LinkedChain fold). -/
def mfProjection : ProjectionInclusion 3 :=
  projectionOfLinkedChain mfLinked

/-- Agrees with the historical two-hop special case. -/
theorem mfProjection_eq_linkedTwo :
    mfProjection = projectionOfLinkedTwo mfStep01 mfStep1R mfLink1R :=
  projectionOfLinkedChain_two mfStep01 mfStep1R mfLink1R

theorem mf_no_empty_of_projection :
    ¬ mfProjection.gClosure.mem [] :=
  no_empty_of_projection mfProjection mfR_no_empty

def mfDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-CYCLE-TWO-CHORDS-001/PROOF_PROJECTION_E4.md"

end PNPLab.Resolution
