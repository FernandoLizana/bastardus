/-
  Fresh G₀→R for non-pack alt1: C_5 + chords (0,2),(1,4).

  Machine fact: Closure₃(G) has size 42 and excludes □; residual
  `alt1RClosed` (16) excludes □; every Closure₃(G) clause supported on
  residual edge vars lies in `alt1RClosed`.

  Beyond pack-canonical ofold (chords (0,2),(1,3)): same |G|→|R| shape,
  distinct global `_edge_var_map` labeling.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures
import PNPLab.AltResidualClosures

namespace PNPLab.Resolution

def alt1GAxioms : List Clause :=
  [ [(-7 : Lit), (6 : Lit)]
  , [(-6 : Lit), (7 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-7 : Lit), (3 : Lit), (5 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-6 : Lit), (2 : Lit), (4 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (3 : Lit), (7 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (2 : Lit), (6 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (5 : Lit), (7 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (4 : Lit), (6 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def alt1GClosed : List Clause :=
  [ [(-7 : Lit), (6 : Lit)]
  , [(-6 : Lit), (7 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (6 : Lit)]
  , [(-7 : Lit), (2 : Lit), (4 : Lit)]
  , [(-7 : Lit), (2 : Lit), (6 : Lit)]
  , [(-7 : Lit), (3 : Lit), (5 : Lit)]
  , [(-7 : Lit), (3 : Lit), (6 : Lit)]
  , [(-7 : Lit), (4 : Lit), (6 : Lit)]
  , [(-7 : Lit), (5 : Lit), (6 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-6 : Lit), (2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (2 : Lit), (7 : Lit)]
  , [(-6 : Lit), (3 : Lit), (5 : Lit)]
  , [(-6 : Lit), (3 : Lit), (7 : Lit)]
  , [(-6 : Lit), (4 : Lit), (7 : Lit)]
  , [(-6 : Lit), (5 : Lit), (7 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (3 : Lit), (6 : Lit)]
  , [(-5 : Lit), (3 : Lit), (7 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (2 : Lit), (6 : Lit)]
  , [(-4 : Lit), (2 : Lit), (7 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (5 : Lit), (6 : Lit)]
  , [(-3 : Lit), (5 : Lit), (7 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (4 : Lit), (6 : Lit)]
  , [(-2 : Lit), (4 : Lit), (7 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

/-- Pivot range covering all alt1 G₀ literals. -/
def alt1GPivots : List Lit := [-10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- Residual vars (must match `alt1Vres`). -/
def alt1GVres : List Nat := [1, 2, 3, 4, 5, 7]

theorem alt1GVres_eq_alt1 : alt1GVres = alt1Vres := by native_decide

def alt1GClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem alt1G_closed_bool : alt1GClosedUnder alt1GClosed 3 alt1GPivots = true := by
  native_decide

theorem alt1G_lits_in_pivots :
    (alt1GClosed.all fun C => C.all fun lit => decide (lit ∈ alt1GPivots)) = true := by
  native_decide

theorem alt1G_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ alt1GClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ alt1GPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp alt1G_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem alt1G_mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : alt1GClosedUnder S w pivots = true)
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

def alt1GClosure : WidthClosure 3 where
  axioms := alt1GAxioms
  mem := fun C => C ∈ alt1GClosed
  axiom_mem := by
    intro C hC _
    have h : (alt1GAxioms.all fun A => alt1GClosed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact alt1G_mem_of_closed alt1G_closed_bool hC hD hRes hw (alt1G_pivot hC hRes)

theorem alt1G_no_empty : ¬ alt1GClosure.mem [] := by
  simp [alt1GClosure]
  native_decide

def alt1GProjOK : Bool :=
  alt1GClosed.all fun C =>
    !(supportedOn C alt1Vres) || alt1RClosed.contains C

theorem alt1GProjOK_true : alt1GProjOK = true := by native_decide

theorem alt1G_supported_in_R
    {C : Clause} (hG : C ∈ alt1GClosed) (hsup : supportedOn C alt1Vres = true) :
    C ∈ alt1RClosed := by
  have hall := (List.all_eq_true.mp alt1GProjOK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

/-- Fresh instance G₀ → residual R (beyond pack routing / R→R self-proj). -/
def alt1GProjection : ProjectionInclusion 3 where
  gClosure := alt1GClosure
  rClosure := alt1RClosure
  Vres := alt1Vres
  holds := fun _ hG hsup => alt1G_supported_in_R hG hsup

def alt1GEliminationStep : EliminationStep 3 where
  before := alt1GClosure
  after := alt1RClosure
  V_after := alt1Vres
  preserves := fun _ hB hsup => alt1G_supported_in_R hB hsup

theorem alt1G_no_empty_of_projection :
    ¬ alt1GProjection.gClosure.mem [] :=
  no_empty_of_projection alt1GProjection alt1R_closure_no_empty

/-- Fresh G₀→R beyond packs, with residual ≅ template residualAxioms. -/
theorem alt1_fresh_g0_projects (e : Bicyclic.CrossingEndpoints) :
    topologySetEq alt1TopologyRename alt1RClosed = true ∧
      residualAxioms e = k4Axioms ∧
      ¬ alt1GProjection.gClosure.mem [] :=
  ⟨(alt1_global_edge_iso_to_residualAxioms e).1,
    (alt1_global_edge_iso_to_residualAxioms e).2,
    alt1G_no_empty_of_projection⟩

def alt1GDoc : String :=
  "fresh G₀ Closure₃ for alt1; ProjectionInclusion beyond packs"

end PNPLab.Resolution
