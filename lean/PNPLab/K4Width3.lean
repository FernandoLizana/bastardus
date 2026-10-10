/-
  Odd-charge K₄ Tseitin as a width-3 closure (Category C).

  Machine fact: Closure₃(T(K₄, odd)) has size 16 = #axioms and excludes □;
  Width = 4 (empty appears only at width 4). Packaged for ProjectionInclusion.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures

namespace PNPLab.Resolution

def k4Axioms : List Clause :=
  [ [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-2 : Lit), (4 : Lit), (6 : Lit)]
  , [(-4 : Lit), (2 : Lit), (6 : Lit)]
  , [(-6 : Lit), (2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-3 : Lit), (5 : Lit), (6 : Lit)]
  , [(-5 : Lit), (3 : Lit), (6 : Lit)]
  , [(-6 : Lit), (3 : Lit), (5 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-3 : Lit)]
  ]

/-- At width 3 the saturated set equals the axiom list (no □). -/
abbrev k4Closed : List Clause := k4Axioms

def k4Pivots : List Lit := [-7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7]

def k4ClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem k4_closed_bool : k4ClosedUnder k4Closed 3 k4Pivots = true := by
  native_decide

theorem k4_lits_in_pivots :
    (k4Closed.all fun C => C.all fun lit => decide (lit ∈ k4Pivots)) = true := by
  native_decide

theorem k4_pivot_in
    {C D R : Clause} {p : Lit}
    (hC : C ∈ k4Closed) (hRes : resolveOriented C D p = some R) :
    p ∈ k4Pivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp k4_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem k4_mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : k4ClosedUnder S w pivots = true)
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

def k4Closure : WidthClosure 3 where
  axioms := k4Axioms
  mem := fun C => C ∈ k4Closed
  axiom_mem := by
    intro C hC _
    -- axioms ≡ closed
    simpa [k4Closed] using hC
  closed := by
    intro C D R p hC hD hRes hw
    exact k4_mem_of_closed k4_closed_bool hC hD hRes hw (k4_pivot_in hC hRes)

theorem k4_no_empty : ¬ k4Closure.mem [] := by
  simp [k4Closure, k4Closed, k4Axioms]

/-- Self-projection of the K₄ width-3 closure (restriction lemma instance). -/
def k4SelfProjection : ProjectionInclusion 3 :=
  selfProjection 3 k4Closure [1, 2, 3, 4, 5, 6]

theorem k4_no_empty_of_self_projection :
    ¬ k4SelfProjection.gClosure.mem [] :=
  no_empty_of_projection k4SelfProjection k4_no_empty

def k4EliminationChain : EliminationChain 3 where
  steps := [identityElimination 3 k4Closure [1, 2, 3, 4, 5, 6]]
  certDoc := "lean/PNPLab/K4Width3.lean"

def k4LowerBoundDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-CYCLE-TWO-CHORDS-001/LIFT_K4.md"

end PNPLab.Resolution
