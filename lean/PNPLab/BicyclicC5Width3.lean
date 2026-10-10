/-
  Bicyclic upper bound: C₅ + chord (0,2), odd charge, Width ≤ 3 = Δ.
  Full Closure₃ size 233 contains □.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures

namespace PNPLab.Resolution

def bi5Axioms : List Clause :=
  [ [(-6 : Lit), (3 : Lit)]
  , [(-6 : Lit), (5 : Lit)]
  , [(-5 : Lit), (6 : Lit)]
  , [(-4 : Lit), (1 : Lit)]
  , [(-3 : Lit), (6 : Lit)]
  , [(-1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-5 : Lit), (2 : Lit), (4 : Lit)]
  , [(-4 : Lit), (2 : Lit), (5 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (4 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def bi5Closed : List Clause :=
  [ []
  , [(-6 : Lit)]
  , [(-5 : Lit)]
  , [(-4 : Lit)]
  , [(-3 : Lit)]
  , [(-2 : Lit)]
  , [(-1 : Lit)]
  , [(1 : Lit)]
  , [(2 : Lit)]
  , [(3 : Lit)]
  , [(4 : Lit)]
  , [(5 : Lit)]
  , [(6 : Lit)]
  , [(-6 : Lit), (-5 : Lit)]
  , [(-6 : Lit), (-4 : Lit)]
  , [(-6 : Lit), (-3 : Lit)]
  , [(-6 : Lit), (-2 : Lit)]
  , [(-6 : Lit), (-1 : Lit)]
  , [(-6 : Lit), (1 : Lit)]
  , [(-6 : Lit), (2 : Lit)]
  , [(-6 : Lit), (3 : Lit)]
  , [(-6 : Lit), (4 : Lit)]
  , [(-6 : Lit), (5 : Lit)]
  , [(-5 : Lit), (-4 : Lit)]
  , [(-5 : Lit), (-3 : Lit)]
  , [(-5 : Lit), (-2 : Lit)]
  , [(-5 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (1 : Lit)]
  , [(-5 : Lit), (2 : Lit)]
  , [(-5 : Lit), (3 : Lit)]
  , [(-5 : Lit), (4 : Lit)]
  , [(-5 : Lit), (6 : Lit)]
  , [(-4 : Lit), (-3 : Lit)]
  , [(-4 : Lit), (-2 : Lit)]
  , [(-4 : Lit), (-1 : Lit)]
  , [(-4 : Lit), (1 : Lit)]
  , [(-4 : Lit), (2 : Lit)]
  , [(-4 : Lit), (3 : Lit)]
  , [(-4 : Lit), (5 : Lit)]
  , [(-4 : Lit), (6 : Lit)]
  , [(-3 : Lit), (-2 : Lit)]
  , [(-3 : Lit), (-1 : Lit)]
  , [(-3 : Lit), (1 : Lit)]
  , [(-3 : Lit), (2 : Lit)]
  , [(-3 : Lit), (4 : Lit)]
  , [(-3 : Lit), (5 : Lit)]
  , [(-3 : Lit), (6 : Lit)]
  , [(-2 : Lit), (-1 : Lit)]
  , [(-2 : Lit), (1 : Lit)]
  , [(-2 : Lit), (3 : Lit)]
  , [(-2 : Lit), (4 : Lit)]
  , [(-2 : Lit), (5 : Lit)]
  , [(-2 : Lit), (6 : Lit)]
  , [(-1 : Lit), (2 : Lit)]
  , [(-1 : Lit), (3 : Lit)]
  , [(-1 : Lit), (4 : Lit)]
  , [(-1 : Lit), (5 : Lit)]
  , [(-1 : Lit), (6 : Lit)]
  , [(1 : Lit), (2 : Lit)]
  , [(1 : Lit), (3 : Lit)]
  , [(1 : Lit), (4 : Lit)]
  , [(1 : Lit), (5 : Lit)]
  , [(1 : Lit), (6 : Lit)]
  , [(2 : Lit), (3 : Lit)]
  , [(2 : Lit), (4 : Lit)]
  , [(2 : Lit), (5 : Lit)]
  , [(2 : Lit), (6 : Lit)]
  , [(3 : Lit), (4 : Lit)]
  , [(3 : Lit), (5 : Lit)]
  , [(3 : Lit), (6 : Lit)]
  , [(4 : Lit), (5 : Lit)]
  , [(4 : Lit), (6 : Lit)]
  , [(5 : Lit), (6 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-4 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-2 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (1 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (2 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (4 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (-3 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (1 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (2 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (3 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (5 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (-2 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (-1 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (1 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (2 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (4 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (5 : Lit)]
  , [(-6 : Lit), (-2 : Lit), (-1 : Lit)]
  , [(-6 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-6 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-6 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (-2 : Lit), (5 : Lit)]
  , [(-6 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-6 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-6 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-6 : Lit), (-1 : Lit), (5 : Lit)]
  , [(-6 : Lit), (1 : Lit), (2 : Lit)]
  , [(-6 : Lit), (1 : Lit), (3 : Lit)]
  , [(-6 : Lit), (1 : Lit), (4 : Lit)]
  , [(-6 : Lit), (1 : Lit), (5 : Lit)]
  , [(-6 : Lit), (2 : Lit), (3 : Lit)]
  , [(-6 : Lit), (2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (2 : Lit), (5 : Lit)]
  , [(-6 : Lit), (3 : Lit), (4 : Lit)]
  , [(-6 : Lit), (3 : Lit), (5 : Lit)]
  , [(-6 : Lit), (4 : Lit), (5 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-3 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (1 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (2 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (3 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (6 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (-2 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (1 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (2 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (4 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (6 : Lit)]
  , [(-5 : Lit), (-2 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-5 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-5 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-5 : Lit), (-2 : Lit), (6 : Lit)]
  , [(-5 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-5 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-5 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (-1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (1 : Lit), (2 : Lit)]
  , [(-5 : Lit), (1 : Lit), (3 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (2 : Lit), (3 : Lit)]
  , [(-5 : Lit), (2 : Lit), (4 : Lit)]
  , [(-5 : Lit), (2 : Lit), (6 : Lit)]
  , [(-5 : Lit), (3 : Lit), (4 : Lit)]
  , [(-5 : Lit), (3 : Lit), (6 : Lit)]
  , [(-5 : Lit), (4 : Lit), (6 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (-2 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (-1 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (1 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (2 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (5 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (6 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (-1 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (5 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (6 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (6 : Lit)]
  , [(-4 : Lit), (1 : Lit), (2 : Lit)]
  , [(-4 : Lit), (1 : Lit), (3 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (1 : Lit), (6 : Lit)]
  , [(-4 : Lit), (2 : Lit), (3 : Lit)]
  , [(-4 : Lit), (2 : Lit), (5 : Lit)]
  , [(-4 : Lit), (2 : Lit), (6 : Lit)]
  , [(-4 : Lit), (3 : Lit), (5 : Lit)]
  , [(-4 : Lit), (3 : Lit), (6 : Lit)]
  , [(-4 : Lit), (5 : Lit), (6 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (-1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (5 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (6 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (5 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (6 : Lit)]
  , [(-3 : Lit), (1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (1 : Lit), (4 : Lit)]
  , [(-3 : Lit), (1 : Lit), (5 : Lit)]
  , [(-3 : Lit), (1 : Lit), (6 : Lit)]
  , [(-3 : Lit), (2 : Lit), (4 : Lit)]
  , [(-3 : Lit), (2 : Lit), (5 : Lit)]
  , [(-3 : Lit), (2 : Lit), (6 : Lit)]
  , [(-3 : Lit), (4 : Lit), (5 : Lit)]
  , [(-3 : Lit), (4 : Lit), (6 : Lit)]
  , [(-3 : Lit), (5 : Lit), (6 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (5 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (6 : Lit)]
  , [(-2 : Lit), (1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (1 : Lit), (4 : Lit)]
  , [(-2 : Lit), (1 : Lit), (5 : Lit)]
  , [(-2 : Lit), (1 : Lit), (6 : Lit)]
  , [(-2 : Lit), (3 : Lit), (4 : Lit)]
  , [(-2 : Lit), (3 : Lit), (5 : Lit)]
  , [(-2 : Lit), (3 : Lit), (6 : Lit)]
  , [(-2 : Lit), (4 : Lit), (5 : Lit)]
  , [(-2 : Lit), (4 : Lit), (6 : Lit)]
  , [(-2 : Lit), (5 : Lit), (6 : Lit)]
  , [(-1 : Lit), (2 : Lit), (3 : Lit)]
  , [(-1 : Lit), (2 : Lit), (4 : Lit)]
  , [(-1 : Lit), (2 : Lit), (5 : Lit)]
  , [(-1 : Lit), (2 : Lit), (6 : Lit)]
  , [(-1 : Lit), (3 : Lit), (4 : Lit)]
  , [(-1 : Lit), (3 : Lit), (5 : Lit)]
  , [(-1 : Lit), (3 : Lit), (6 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(-1 : Lit), (4 : Lit), (6 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(1 : Lit), (2 : Lit), (4 : Lit)]
  , [(1 : Lit), (2 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit), (6 : Lit)]
  , [(1 : Lit), (3 : Lit), (4 : Lit)]
  , [(1 : Lit), (3 : Lit), (5 : Lit)]
  , [(1 : Lit), (3 : Lit), (6 : Lit)]
  , [(1 : Lit), (4 : Lit), (5 : Lit)]
  , [(1 : Lit), (4 : Lit), (6 : Lit)]
  , [(1 : Lit), (5 : Lit), (6 : Lit)]
  , [(2 : Lit), (3 : Lit), (4 : Lit)]
  , [(2 : Lit), (3 : Lit), (5 : Lit)]
  , [(2 : Lit), (3 : Lit), (6 : Lit)]
  , [(2 : Lit), (4 : Lit), (5 : Lit)]
  , [(2 : Lit), (4 : Lit), (6 : Lit)]
  , [(2 : Lit), (5 : Lit), (6 : Lit)]
  , [(3 : Lit), (4 : Lit), (5 : Lit)]
  , [(3 : Lit), (4 : Lit), (6 : Lit)]
  , [(3 : Lit), (5 : Lit), (6 : Lit)]
  , [(4 : Lit), (5 : Lit), (6 : Lit)]
  ]

def bi5Pivots : List Lit := [-7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7]

def bi5ClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem bi5_closed_bool : bi5ClosedUnder bi5Closed 3 bi5Pivots = true := by
  native_decide

theorem bi5_lits_in_pivots :
    (bi5Closed.all fun C => C.all fun lit => decide (lit ∈ bi5Pivots)) = true := by
  native_decide

theorem bi5_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ bi5Closed) (hRes : resolveOriented C D p = some R) :
    p ∈ bi5Pivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp bi5_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem bi5_mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : bi5ClosedUnder S w pivots = true)
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

def bi5Closure : WidthClosure 3 where
  axioms := bi5Axioms
  mem := fun C => C ∈ bi5Closed
  axiom_mem := by
    intro C hC _
    have h : (bi5Axioms.all fun A => bi5Closed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact bi5_mem_of_closed bi5_closed_bool hC hD hRes hw (bi5_pivot hC hRes)

theorem bi5_has_empty : bi5Closure.mem [] := by
  simp [bi5Closure]
  native_decide

theorem bi5_width_le_delta : bi5Closure.mem [] := bi5_has_empty

def bi5Doc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-BICYCLIC-001/PROOF_PATHFOLD.md"

end PNPLab.Resolution
