/-
  One-fold crossing projection: C_5 + chords (0,2),(1,3) → residual K₄.

  Machine fact: Closure₃(G) has size 42 and excludes □; residual XOR
  Closure₃(R) has size 16 (= axioms) and excludes □; every Closure₃(G)
  clause supported on residual edge vars lies in Closure₃(R).

  Relies on `resolveOriented` rejecting tautological resolvents and normalizing
  survivors (same as Python `_norm` / width saturation).
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures

namespace PNPLab.Resolution

def ofoldGAxioms : List Clause :=
  [ [(-7 : Lit), (3 : Lit)]
  , [(-3 : Lit), (7 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-7 : Lit), (5 : Lit), (6 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-6 : Lit), (2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (5 : Lit), (7 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (6 : Lit), (7 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (2 : Lit), (6 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (4 : Lit), (6 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def ofoldGClosed : List Clause :=
  [ [(-7 : Lit), (3 : Lit)]
  , [(-3 : Lit), (7 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-7 : Lit), (1 : Lit), (3 : Lit)]
  , [(-7 : Lit), (2 : Lit), (3 : Lit)]
  , [(-7 : Lit), (3 : Lit), (5 : Lit)]
  , [(-7 : Lit), (3 : Lit), (6 : Lit)]
  , [(-7 : Lit), (5 : Lit), (6 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (7 : Lit)]
  , [(-6 : Lit), (2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (3 : Lit), (5 : Lit)]
  , [(-6 : Lit), (5 : Lit), (7 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (7 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (3 : Lit), (6 : Lit)]
  , [(-5 : Lit), (6 : Lit), (7 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (2 : Lit), (6 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-3 : Lit), (1 : Lit), (7 : Lit)]
  , [(-3 : Lit), (2 : Lit), (7 : Lit)]
  , [(-3 : Lit), (5 : Lit), (6 : Lit)]
  , [(-3 : Lit), (5 : Lit), (7 : Lit)]
  , [(-3 : Lit), (6 : Lit), (7 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-2 : Lit), (4 : Lit), (6 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(1 : Lit), (2 : Lit), (7 : Lit)]
  ]

def ofoldRAxioms : List Clause :=
  [ [(-6 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-6 : Lit), (2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (3 : Lit), (5 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (3 : Lit), (6 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (2 : Lit), (6 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (5 : Lit), (6 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (4 : Lit), (6 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

/-- Residual width-3 closure equals residual XOR axioms. -/
abbrev ofoldRClosed : List Clause := ofoldRAxioms

def ofoldPivots : List Lit := [-8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8]

def ofoldVres : List Nat := [1, 2, 3, 4, 5, 6]

def ofoldClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem ofoldG_closed_bool : ofoldClosedUnder ofoldGClosed 3 ofoldPivots = true := by
  native_decide

theorem ofoldR_closed_bool : ofoldClosedUnder ofoldRClosed 3 ofoldPivots = true := by
  native_decide

theorem ofoldG_lits_in_pivots :
    (ofoldGClosed.all fun C => C.all fun lit => decide (lit ∈ ofoldPivots)) = true := by
  native_decide

theorem ofoldR_lits_in_pivots :
    (ofoldRClosed.all fun C => C.all fun lit => decide (lit ∈ ofoldPivots)) = true := by
  native_decide

theorem ofold_pivot_G
    {C D R : Clause} {p : Lit}
    (hC : C ∈ ofoldGClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ ofoldPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp ofoldG_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem ofold_pivot_R
    {C D R : Clause} {p : Lit}
    (hC : C ∈ ofoldRClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ ofoldPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp ofoldR_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem ofold_mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : ofoldClosedUnder S w pivots = true)
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

def ofoldGClosure : WidthClosure 3 where
  axioms := ofoldGAxioms
  mem := fun C => C ∈ ofoldGClosed
  axiom_mem := by
    intro C hC _
    -- every axiom is present in the enumerated Closure₃
    have h : (ofoldGAxioms.all fun A => ofoldGClosed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact ofold_mem_of_closed ofoldG_closed_bool hC hD hRes hw (ofold_pivot_G hC hRes)

def ofoldRClosure : WidthClosure 3 where
  axioms := ofoldRAxioms
  mem := fun C => C ∈ ofoldRClosed
  axiom_mem := by
    intro C hC _
    simpa [ofoldRClosed] using hC
  closed := by
    intro C D R p hC hD hRes hw
    exact ofold_mem_of_closed ofoldR_closed_bool hC hD hRes hw (ofold_pivot_R hC hRes)

theorem ofoldG_no_empty : ¬ ofoldGClosure.mem [] := by
  simp [ofoldGClosure]
  native_decide

theorem ofoldR_no_empty : ¬ ofoldRClosure.mem [] := by
  simp [ofoldRClosure, ofoldRClosed]
  native_decide

def ofoldProjOK : Bool :=
  ofoldGClosed.all fun C =>
    !(supportedOn C ofoldVres) || ofoldRClosed.contains C

theorem ofoldProjOK_true : ofoldProjOK = true := by native_decide

theorem ofold_supported_in_R
    {C : Clause} (hG : C ∈ ofoldGClosed) (hsup : supportedOn C ofoldVres = true) :
    C ∈ ofoldRClosed := by
  have hall := (List.all_eq_true.mp ofoldProjOK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

def ofoldProjection : ProjectionInclusion 3 where
  gClosure := ofoldGClosure
  rClosure := ofoldRClosure
  Vres := ofoldVres
  holds := fun _ hG hsup => ofold_supported_in_R hG hsup

def ofoldEliminationStep : EliminationStep 3 where
  before := ofoldGClosure
  after := ofoldRClosure
  V_after := ofoldVres
  preserves := fun _ hB hsup => ofold_supported_in_R hB hsup

def ofoldEliminationChain : EliminationChain 3 where
  steps := [ofoldEliminationStep]
  certDoc := "lean/PNPLab/OneFoldProjection.lean"

theorem ofold_no_empty_of_projection :
    ¬ ofoldProjection.gClosure.mem [] :=
  no_empty_of_projection ofoldProjection ofoldR_no_empty

def ofoldDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-CYCLE-TWO-CHORDS-001/PROOF_PROJECTION_E4.md"

end PNPLab.Resolution
