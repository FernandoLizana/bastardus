/-
  Fresh G₀→R for non-pack alt3: C_7 + chords [0, 2],[1, 3] (hop 3).

  Machine fact: Closure₃(G) has size 172 and excludes □; residual
  `alt3RClosed` (16) excludes □; every Closure₃(G) clause supported on
  residual edge vars lies in `alt3RClosed`.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures
import PNPLab.AltResidualClosures

namespace PNPLab.Resolution

def alt3GAxioms : List Clause :=
  [ [(-9 : Lit), (3 : Lit)]
  , [(-9 : Lit), (8 : Lit)]
  , [(-8 : Lit), (7 : Lit)]
  , [(-8 : Lit), (9 : Lit)]
  , [(-7 : Lit), (8 : Lit)]
  , [(-3 : Lit), (9 : Lit)]
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

def alt3GClosed : List Clause :=
  [ [(-9 : Lit), (3 : Lit)]
  , [(-9 : Lit), (7 : Lit)]
  , [(-9 : Lit), (8 : Lit)]
  , [(-8 : Lit), (3 : Lit)]
  , [(-8 : Lit), (7 : Lit)]
  , [(-8 : Lit), (9 : Lit)]
  , [(-7 : Lit), (3 : Lit)]
  , [(-7 : Lit), (8 : Lit)]
  , [(-7 : Lit), (9 : Lit)]
  , [(-3 : Lit), (7 : Lit)]
  , [(-3 : Lit), (8 : Lit)]
  , [(-3 : Lit), (9 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-9 : Lit), (1 : Lit), (3 : Lit)]
  , [(-9 : Lit), (1 : Lit), (7 : Lit)]
  , [(-9 : Lit), (1 : Lit), (8 : Lit)]
  , [(-9 : Lit), (2 : Lit), (3 : Lit)]
  , [(-9 : Lit), (2 : Lit), (7 : Lit)]
  , [(-9 : Lit), (2 : Lit), (8 : Lit)]
  , [(-9 : Lit), (3 : Lit), (5 : Lit)]
  , [(-9 : Lit), (3 : Lit), (6 : Lit)]
  , [(-9 : Lit), (3 : Lit), (7 : Lit)]
  , [(-9 : Lit), (3 : Lit), (8 : Lit)]
  , [(-9 : Lit), (5 : Lit), (6 : Lit)]
  , [(-9 : Lit), (5 : Lit), (7 : Lit)]
  , [(-9 : Lit), (5 : Lit), (8 : Lit)]
  , [(-9 : Lit), (6 : Lit), (7 : Lit)]
  , [(-9 : Lit), (6 : Lit), (8 : Lit)]
  , [(-9 : Lit), (7 : Lit), (8 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-8 : Lit), (1 : Lit), (3 : Lit)]
  , [(-8 : Lit), (1 : Lit), (7 : Lit)]
  , [(-8 : Lit), (1 : Lit), (9 : Lit)]
  , [(-8 : Lit), (2 : Lit), (3 : Lit)]
  , [(-8 : Lit), (2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (2 : Lit), (9 : Lit)]
  , [(-8 : Lit), (3 : Lit), (5 : Lit)]
  , [(-8 : Lit), (3 : Lit), (6 : Lit)]
  , [(-8 : Lit), (3 : Lit), (7 : Lit)]
  , [(-8 : Lit), (3 : Lit), (9 : Lit)]
  , [(-8 : Lit), (5 : Lit), (6 : Lit)]
  , [(-8 : Lit), (5 : Lit), (7 : Lit)]
  , [(-8 : Lit), (5 : Lit), (9 : Lit)]
  , [(-8 : Lit), (6 : Lit), (7 : Lit)]
  , [(-8 : Lit), (6 : Lit), (9 : Lit)]
  , [(-8 : Lit), (7 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-7 : Lit), (1 : Lit), (3 : Lit)]
  , [(-7 : Lit), (1 : Lit), (8 : Lit)]
  , [(-7 : Lit), (1 : Lit), (9 : Lit)]
  , [(-7 : Lit), (2 : Lit), (3 : Lit)]
  , [(-7 : Lit), (2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (2 : Lit), (9 : Lit)]
  , [(-7 : Lit), (3 : Lit), (5 : Lit)]
  , [(-7 : Lit), (3 : Lit), (6 : Lit)]
  , [(-7 : Lit), (3 : Lit), (8 : Lit)]
  , [(-7 : Lit), (3 : Lit), (9 : Lit)]
  , [(-7 : Lit), (5 : Lit), (6 : Lit)]
  , [(-7 : Lit), (5 : Lit), (8 : Lit)]
  , [(-7 : Lit), (5 : Lit), (9 : Lit)]
  , [(-7 : Lit), (6 : Lit), (8 : Lit)]
  , [(-7 : Lit), (6 : Lit), (9 : Lit)]
  , [(-7 : Lit), (8 : Lit), (9 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-6 : Lit), (2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (3 : Lit), (5 : Lit)]
  , [(-6 : Lit), (5 : Lit), (7 : Lit)]
  , [(-6 : Lit), (5 : Lit), (8 : Lit)]
  , [(-6 : Lit), (5 : Lit), (9 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (7 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (3 : Lit), (6 : Lit)]
  , [(-5 : Lit), (6 : Lit), (7 : Lit)]
  , [(-5 : Lit), (6 : Lit), (8 : Lit)]
  , [(-5 : Lit), (6 : Lit), (9 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (2 : Lit), (6 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-3 : Lit), (1 : Lit), (7 : Lit)]
  , [(-3 : Lit), (1 : Lit), (8 : Lit)]
  , [(-3 : Lit), (1 : Lit), (9 : Lit)]
  , [(-3 : Lit), (2 : Lit), (7 : Lit)]
  , [(-3 : Lit), (2 : Lit), (8 : Lit)]
  , [(-3 : Lit), (2 : Lit), (9 : Lit)]
  , [(-3 : Lit), (5 : Lit), (6 : Lit)]
  , [(-3 : Lit), (5 : Lit), (7 : Lit)]
  , [(-3 : Lit), (5 : Lit), (8 : Lit)]
  , [(-3 : Lit), (5 : Lit), (9 : Lit)]
  , [(-3 : Lit), (6 : Lit), (7 : Lit)]
  , [(-3 : Lit), (6 : Lit), (8 : Lit)]
  , [(-3 : Lit), (6 : Lit), (9 : Lit)]
  , [(-3 : Lit), (7 : Lit), (8 : Lit)]
  , [(-3 : Lit), (7 : Lit), (9 : Lit)]
  , [(-3 : Lit), (8 : Lit), (9 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-2 : Lit), (4 : Lit), (6 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(1 : Lit), (2 : Lit), (7 : Lit)]
  , [(1 : Lit), (2 : Lit), (8 : Lit)]
  , [(1 : Lit), (2 : Lit), (9 : Lit)]
  ]

def alt3GPivots : List Lit := [-11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

def alt3GVres : List Nat := [1, 2, 4, 5, 6, 8]

theorem alt3GVres_eq_alt : alt3GVres = alt3Vres := by native_decide

def alt3GClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem alt3G_closed_bool : alt3GClosedUnder alt3GClosed 3 alt3GPivots = true := by
  native_decide

theorem alt3G_lits_in_pivots :
    (alt3GClosed.all fun C => C.all fun lit => decide (lit ∈ alt3GPivots)) = true := by
  native_decide

theorem alt3G_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ alt3GClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ alt3GPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp alt3G_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem alt3G_mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : alt3GClosedUnder S w pivots = true)
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

def alt3GClosure : WidthClosure 3 where
  axioms := alt3GAxioms
  mem := fun C => C ∈ alt3GClosed
  axiom_mem := by
    intro C hC _
    have h : (alt3GAxioms.all fun A => alt3GClosed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact alt3G_mem_of_closed alt3G_closed_bool hC hD hRes hw (alt3G_pivot hC hRes)

theorem alt3G_no_empty : ¬ alt3GClosure.mem [] := by
  simp [alt3GClosure]
  native_decide

def alt3GProjOK : Bool :=
  alt3GClosed.all fun C =>
    !(supportedOn C alt3Vres) || alt3RClosed.contains C

theorem alt3GProjOK_true : alt3GProjOK = true := by native_decide

theorem alt3G_supported_in_R
    {C : Clause} (hG : C ∈ alt3GClosed) (hsup : supportedOn C alt3Vres = true) :
    C ∈ alt3RClosed := by
  have hall := (List.all_eq_true.mp alt3GProjOK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

def alt3GProjection : ProjectionInclusion 3 where
  gClosure := alt3GClosure
  rClosure := alt3RClosure
  Vres := alt3Vres
  holds := fun _ hG hsup => alt3G_supported_in_R hG hsup

def alt3GEliminationStep : EliminationStep 3 where
  before := alt3GClosure
  after := alt3RClosure
  V_after := alt3Vres
  preserves := fun _ hB hsup => alt3G_supported_in_R hB hsup

theorem alt3G_no_empty_of_projection :
    ¬ alt3GProjection.gClosure.mem [] :=
  no_empty_of_projection alt3GProjection alt3R_closure_no_empty

theorem alt3_fresh_g0_projects (e : Bicyclic.CrossingEndpoints) :
    topologySetEq alt3TopologyRename alt3RClosed = true ∧
      residualAxioms e = k4Axioms ∧
      ¬ alt3GProjection.gClosure.mem [] :=
  ⟨(alt3_global_edge_iso_to_residualAxioms e).1,
    (alt3_global_edge_iso_to_residualAxioms e).2,
    alt3G_no_empty_of_projection⟩

def alt3GDoc : String :=
  "fresh G₀ Closure₃ for alt3; ProjectionInclusion beyond packs"

end PNPLab.Resolution
