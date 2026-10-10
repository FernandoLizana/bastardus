/-
  Fresh G₀→R for hop-3 sample samp30: C_7 + chords [0, 4],[3, 6].

  Machine fact: Closure₃(G) has size 118 and excludes □; residual
  `samp30RClosed` (16) excludes □; every Closure₃(G) clause supported on
  residual edge vars lies in `samp30RClosed`.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures
import PNPLab.SampleResidualClosures

namespace PNPLab.Resolution

def samp30GAxioms : List Clause :=
  [ [(-9 : Lit), (8 : Lit)]
  , [(-8 : Lit), (9 : Lit)]
  , [(-5 : Lit), (4 : Lit)]
  , [(-4 : Lit), (1 : Lit)]
  , [(-4 : Lit), (5 : Lit)]
  , [(-1 : Lit), (4 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (-3 : Lit)]
  , [(-9 : Lit), (3 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (2 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-7 : Lit), (3 : Lit), (9 : Lit)]
  , [(-7 : Lit), (5 : Lit), (6 : Lit)]
  , [(-6 : Lit), (2 : Lit), (8 : Lit)]
  , [(-6 : Lit), (5 : Lit), (7 : Lit)]
  , [(-5 : Lit), (6 : Lit), (7 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (7 : Lit), (9 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (6 : Lit), (8 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def samp30GClosed : List Clause :=
  [ [(-9 : Lit), (8 : Lit)]
  , [(-8 : Lit), (9 : Lit)]
  , [(-5 : Lit), (1 : Lit)]
  , [(-5 : Lit), (4 : Lit)]
  , [(-4 : Lit), (1 : Lit)]
  , [(-4 : Lit), (5 : Lit)]
  , [(-1 : Lit), (4 : Lit)]
  , [(-1 : Lit), (5 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (-3 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-9 : Lit), (2 : Lit), (6 : Lit)]
  , [(-9 : Lit), (2 : Lit), (8 : Lit)]
  , [(-9 : Lit), (3 : Lit), (7 : Lit)]
  , [(-9 : Lit), (3 : Lit), (8 : Lit)]
  , [(-9 : Lit), (6 : Lit), (8 : Lit)]
  , [(-9 : Lit), (7 : Lit), (8 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (-3 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-8 : Lit), (2 : Lit), (6 : Lit)]
  , [(-8 : Lit), (2 : Lit), (9 : Lit)]
  , [(-8 : Lit), (3 : Lit), (7 : Lit)]
  , [(-8 : Lit), (3 : Lit), (9 : Lit)]
  , [(-8 : Lit), (6 : Lit), (9 : Lit)]
  , [(-8 : Lit), (7 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-4 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-1 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (1 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (4 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (1 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (5 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (5 : Lit)]
  , [(-7 : Lit), (1 : Lit), (6 : Lit)]
  , [(-7 : Lit), (3 : Lit), (8 : Lit)]
  , [(-7 : Lit), (3 : Lit), (9 : Lit)]
  , [(-7 : Lit), (4 : Lit), (6 : Lit)]
  , [(-7 : Lit), (5 : Lit), (6 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (1 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (4 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (1 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (5 : Lit)]
  , [(-6 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-6 : Lit), (-1 : Lit), (5 : Lit)]
  , [(-6 : Lit), (1 : Lit), (7 : Lit)]
  , [(-6 : Lit), (2 : Lit), (8 : Lit)]
  , [(-6 : Lit), (2 : Lit), (9 : Lit)]
  , [(-6 : Lit), (4 : Lit), (7 : Lit)]
  , [(-6 : Lit), (5 : Lit), (7 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (1 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (1 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (2 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (4 : Lit)]
  , [(-5 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-5 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-5 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-5 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (1 : Lit), (2 : Lit)]
  , [(-5 : Lit), (1 : Lit), (3 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (1 : Lit), (7 : Lit)]
  , [(-5 : Lit), (2 : Lit), (4 : Lit)]
  , [(-5 : Lit), (3 : Lit), (4 : Lit)]
  , [(-5 : Lit), (4 : Lit), (6 : Lit)]
  , [(-5 : Lit), (4 : Lit), (7 : Lit)]
  , [(-5 : Lit), (6 : Lit), (7 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (1 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (2 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (5 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (5 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (1 : Lit), (2 : Lit)]
  , [(-4 : Lit), (1 : Lit), (3 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (1 : Lit), (6 : Lit)]
  , [(-4 : Lit), (1 : Lit), (7 : Lit)]
  , [(-4 : Lit), (2 : Lit), (5 : Lit)]
  , [(-4 : Lit), (3 : Lit), (5 : Lit)]
  , [(-4 : Lit), (5 : Lit), (6 : Lit)]
  , [(-4 : Lit), (5 : Lit), (7 : Lit)]
  , [(-4 : Lit), (6 : Lit), (7 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (5 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (5 : Lit)]
  , [(-3 : Lit), (7 : Lit), (8 : Lit)]
  , [(-3 : Lit), (7 : Lit), (9 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (5 : Lit)]
  , [(-2 : Lit), (6 : Lit), (8 : Lit)]
  , [(-2 : Lit), (6 : Lit), (9 : Lit)]
  , [(-1 : Lit), (2 : Lit), (4 : Lit)]
  , [(-1 : Lit), (2 : Lit), (5 : Lit)]
  , [(-1 : Lit), (3 : Lit), (4 : Lit)]
  , [(-1 : Lit), (3 : Lit), (5 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(-1 : Lit), (4 : Lit), (6 : Lit)]
  , [(-1 : Lit), (4 : Lit), (7 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(-1 : Lit), (5 : Lit), (7 : Lit)]
  , [(-1 : Lit), (6 : Lit), (7 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(2 : Lit), (3 : Lit), (4 : Lit)]
  , [(2 : Lit), (3 : Lit), (5 : Lit)]
  ]

def samp30GPivots : List Lit := [-11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

def samp30GVres : List Nat := [2, 3, 4, 6, 7, 9]

theorem samp30GVres_eq_samp : samp30GVres = samp30Vres := by native_decide

def samp30GClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem samp30G_closed_bool : samp30GClosedUnder samp30GClosed 3 samp30GPivots = true := by
  native_decide

theorem samp30G_lits_in_pivots :
    (samp30GClosed.all fun C => C.all fun lit => decide (lit ∈ samp30GPivots)) = true := by
  native_decide

theorem samp30G_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ samp30GClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ samp30GPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp samp30G_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem samp30G_mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : samp30GClosedUnder S w pivots = true)
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

def samp30GClosure : WidthClosure 3 where
  axioms := samp30GAxioms
  mem := fun C => C ∈ samp30GClosed
  axiom_mem := by
    intro C hC _
    have h : (samp30GAxioms.all fun A => samp30GClosed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact samp30G_mem_of_closed samp30G_closed_bool hC hD hRes hw (samp30G_pivot hC hRes)

theorem samp30G_no_empty : ¬ samp30GClosure.mem [] := by
  simp [samp30GClosure]
  native_decide

def samp30GProjOK : Bool :=
  samp30GClosed.all fun C =>
    !(supportedOn C samp30Vres) || samp30RClosed.contains C

theorem samp30GProjOK_true : samp30GProjOK = true := by native_decide

theorem samp30G_supported_in_R
    {C : Clause} (hG : C ∈ samp30GClosed) (hsup : supportedOn C samp30Vres = true) :
    C ∈ samp30RClosed := by
  have hall := (List.all_eq_true.mp samp30GProjOK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

def samp30GProjection : ProjectionInclusion 3 where
  gClosure := samp30GClosure
  rClosure := samp30RClosure
  Vres := samp30Vres
  holds := fun _ hG hsup => samp30G_supported_in_R hG hsup

def samp30GEliminationStep : EliminationStep 3 where
  before := samp30GClosure
  after := samp30RClosure
  V_after := samp30Vres
  preserves := fun _ hB hsup => samp30G_supported_in_R hB hsup

theorem samp30G_no_empty_of_projection :
    ¬ samp30GProjection.gClosure.mem [] :=
  no_empty_of_projection samp30GProjection samp30_closure_no_empty

theorem samp30_global_edge_iso_to_residualAxioms (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp30TopologyRename samp30RClosed = true ∧
      residualAxioms e = k4Axioms := by
  refine ⟨?_, residualAxioms_eq_k4 e⟩
  have h := samp30TopologySetEq_true
  simpa [topologySetEq, samp30TopologySetEq] using h

theorem samp30_fresh_g0_projects (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp30TopologyRename samp30RClosed = true ∧
      residualAxioms e = k4Axioms ∧
      ¬ samp30GProjection.gClosure.mem [] :=
  ⟨(samp30_global_edge_iso_to_residualAxioms e).1,
    (samp30_global_edge_iso_to_residualAxioms e).2,
    samp30G_no_empty_of_projection⟩

def samp30GDoc : String :=
  "fresh G₀ Closure₃ for samp30; ProjectionInclusion beyond packs/alts"

end PNPLab.Resolution
