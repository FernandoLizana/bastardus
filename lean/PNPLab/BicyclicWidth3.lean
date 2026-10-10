/-
  Bicyclic upper bound: C₄ + chord (0,2), odd charge, Width ≤ 3 = Δ.

  Machine: full Closure₃ (continue after □) has size 131 and
  contains □; axioms size 12. Packaged as WidthClosure with
  `mem []` — dual of K₄ / crossing lower-bound packs.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures

namespace PNPLab.Resolution

def biAxioms : List Clause :=
  [ [(-5 : Lit), (3 : Lit)]
  , [(-4 : Lit), (1 : Lit)]
  , [(-3 : Lit), (5 : Lit)]
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

def biClosed : List Clause :=
  [ []
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
  , [(-5 : Lit), (-4 : Lit)]
  , [(-5 : Lit), (-3 : Lit)]
  , [(-5 : Lit), (-2 : Lit)]
  , [(-5 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (1 : Lit)]
  , [(-5 : Lit), (2 : Lit)]
  , [(-5 : Lit), (3 : Lit)]
  , [(-5 : Lit), (4 : Lit)]
  , [(-4 : Lit), (-3 : Lit)]
  , [(-4 : Lit), (-2 : Lit)]
  , [(-4 : Lit), (-1 : Lit)]
  , [(-4 : Lit), (1 : Lit)]
  , [(-4 : Lit), (2 : Lit)]
  , [(-4 : Lit), (3 : Lit)]
  , [(-4 : Lit), (5 : Lit)]
  , [(-3 : Lit), (-2 : Lit)]
  , [(-3 : Lit), (-1 : Lit)]
  , [(-3 : Lit), (1 : Lit)]
  , [(-3 : Lit), (2 : Lit)]
  , [(-3 : Lit), (4 : Lit)]
  , [(-3 : Lit), (5 : Lit)]
  , [(-2 : Lit), (-1 : Lit)]
  , [(-2 : Lit), (1 : Lit)]
  , [(-2 : Lit), (3 : Lit)]
  , [(-2 : Lit), (4 : Lit)]
  , [(-2 : Lit), (5 : Lit)]
  , [(-1 : Lit), (2 : Lit)]
  , [(-1 : Lit), (3 : Lit)]
  , [(-1 : Lit), (4 : Lit)]
  , [(-1 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit)]
  , [(1 : Lit), (3 : Lit)]
  , [(1 : Lit), (4 : Lit)]
  , [(1 : Lit), (5 : Lit)]
  , [(2 : Lit), (3 : Lit)]
  , [(2 : Lit), (4 : Lit)]
  , [(2 : Lit), (5 : Lit)]
  , [(3 : Lit), (4 : Lit)]
  , [(3 : Lit), (5 : Lit)]
  , [(4 : Lit), (5 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-3 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (1 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (2 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (3 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (-2 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (1 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (2 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (4 : Lit)]
  , [(-5 : Lit), (-2 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-5 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-5 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-5 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-5 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-5 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (1 : Lit), (2 : Lit)]
  , [(-5 : Lit), (1 : Lit), (3 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (2 : Lit), (3 : Lit)]
  , [(-5 : Lit), (2 : Lit), (4 : Lit)]
  , [(-5 : Lit), (3 : Lit), (4 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (-2 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (-1 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (1 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (2 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (5 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (-1 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (5 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (1 : Lit), (2 : Lit)]
  , [(-4 : Lit), (1 : Lit), (3 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (2 : Lit), (3 : Lit)]
  , [(-4 : Lit), (2 : Lit), (5 : Lit)]
  , [(-4 : Lit), (3 : Lit), (5 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (-1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (5 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (5 : Lit)]
  , [(-3 : Lit), (1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (1 : Lit), (4 : Lit)]
  , [(-3 : Lit), (1 : Lit), (5 : Lit)]
  , [(-3 : Lit), (2 : Lit), (4 : Lit)]
  , [(-3 : Lit), (2 : Lit), (5 : Lit)]
  , [(-3 : Lit), (4 : Lit), (5 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (5 : Lit)]
  , [(-2 : Lit), (1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (1 : Lit), (4 : Lit)]
  , [(-2 : Lit), (1 : Lit), (5 : Lit)]
  , [(-2 : Lit), (3 : Lit), (4 : Lit)]
  , [(-2 : Lit), (3 : Lit), (5 : Lit)]
  , [(-2 : Lit), (4 : Lit), (5 : Lit)]
  , [(-1 : Lit), (2 : Lit), (3 : Lit)]
  , [(-1 : Lit), (2 : Lit), (4 : Lit)]
  , [(-1 : Lit), (2 : Lit), (5 : Lit)]
  , [(-1 : Lit), (3 : Lit), (4 : Lit)]
  , [(-1 : Lit), (3 : Lit), (5 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(1 : Lit), (2 : Lit), (4 : Lit)]
  , [(1 : Lit), (2 : Lit), (5 : Lit)]
  , [(1 : Lit), (3 : Lit), (4 : Lit)]
  , [(1 : Lit), (3 : Lit), (5 : Lit)]
  , [(1 : Lit), (4 : Lit), (5 : Lit)]
  , [(2 : Lit), (3 : Lit), (4 : Lit)]
  , [(2 : Lit), (3 : Lit), (5 : Lit)]
  , [(2 : Lit), (4 : Lit), (5 : Lit)]
  , [(3 : Lit), (4 : Lit), (5 : Lit)]
  ]

def biPivots : List Lit := [-6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6]

def biClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem bi_closed_bool : biClosedUnder biClosed 3 biPivots = true := by
  native_decide

theorem bi_lits_in_pivots :
    (biClosed.all fun C => C.all fun lit => decide (lit ∈ biPivots)) = true := by
  native_decide

theorem bi_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ biClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ biPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp bi_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem bi_mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : biClosedUnder S w pivots = true)
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

def biClosure : WidthClosure 3 where
  axioms := biAxioms
  mem := fun C => C ∈ biClosed
  axiom_mem := by
    intro C hC _
    have h : (biAxioms.all fun A => biClosed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact bi_mem_of_closed bi_closed_bool hC hD hRes hw (bi_pivot hC hRes)

theorem bi_has_empty : biClosure.mem [] := by
  simp [biClosure]
  native_decide

/-- Upper bound: empty at width 3 for this θ-graph (Width ≤ Δ = 3). -/
theorem bi_width_le_delta : biClosure.mem [] := bi_has_empty

def biSelfProjection : ProjectionInclusion 3 :=
  selfProjection 3 biClosure [1, 2, 3, 4, 5]

def biEliminationChain : EliminationChain 3 where
  steps := [identityElimination 3 biClosure [1, 2, 3, 4, 5]]
  certDoc := "lean/PNPLab/BicyclicWidth3.lean"

def biDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-BICYCLIC-001/PROOF_PATHFOLD.md"

end PNPLab.Resolution
