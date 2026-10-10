/-
  Fresh G₀→R for hop-2 sample samp8: C_6 + chords [0, 3],[2, 4].

  Machine fact: Closure₃(G) has size 80 and excludes □; residual
  `samp8RClosed` (16) excludes □; every Closure₃(G) clause supported on
  residual edge vars lies in `samp8RClosed`.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures
import PNPLab.SampleResidualClosures

namespace PNPLab.Resolution

def samp8GAxioms : List Clause :=
  [ [(-8 : Lit), (3 : Lit)]
  , [(-4 : Lit), (1 : Lit)]
  , [(-3 : Lit), (8 : Lit)]
  , [(-1 : Lit), (4 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (-6 : Lit)]
  , [(-8 : Lit), (6 : Lit), (7 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (-2 : Lit)]
  , [(-7 : Lit), (2 : Lit), (5 : Lit)]
  , [(-7 : Lit), (6 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-4 : Lit)]
  , [(-6 : Lit), (4 : Lit), (5 : Lit)]
  , [(-6 : Lit), (7 : Lit), (8 : Lit)]
  , [(-5 : Lit), (2 : Lit), (7 : Lit)]
  , [(-5 : Lit), (4 : Lit), (6 : Lit)]
  , [(-4 : Lit), (5 : Lit), (6 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (5 : Lit), (7 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def samp8GClosed : List Clause :=
  [ [(-8 : Lit), (3 : Lit)]
  , [(-4 : Lit), (1 : Lit)]
  , [(-3 : Lit), (8 : Lit)]
  , [(-1 : Lit), (4 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (-6 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-4 : Lit), (1 : Lit)]
  , [(-8 : Lit), (-4 : Lit), (2 : Lit)]
  , [(-8 : Lit), (-4 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-8 : Lit), (1 : Lit), (3 : Lit)]
  , [(-8 : Lit), (2 : Lit), (3 : Lit)]
  , [(-8 : Lit), (3 : Lit), (4 : Lit)]
  , [(-8 : Lit), (3 : Lit), (6 : Lit)]
  , [(-8 : Lit), (3 : Lit), (7 : Lit)]
  , [(-8 : Lit), (6 : Lit), (7 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-3 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (-2 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-7 : Lit), (2 : Lit), (5 : Lit)]
  , [(-7 : Lit), (3 : Lit), (6 : Lit)]
  , [(-7 : Lit), (6 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-4 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (1 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-6 : Lit), (1 : Lit), (5 : Lit)]
  , [(-6 : Lit), (3 : Lit), (7 : Lit)]
  , [(-6 : Lit), (4 : Lit), (5 : Lit)]
  , [(-6 : Lit), (7 : Lit), (8 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (1 : Lit)]
  , [(-5 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (2 : Lit), (7 : Lit)]
  , [(-5 : Lit), (4 : Lit), (6 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (1 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (2 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-4 : Lit), (1 : Lit), (2 : Lit)]
  , [(-4 : Lit), (1 : Lit), (3 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (1 : Lit), (6 : Lit)]
  , [(-4 : Lit), (1 : Lit), (8 : Lit)]
  , [(-4 : Lit), (5 : Lit), (6 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-3 : Lit), (1 : Lit), (8 : Lit)]
  , [(-3 : Lit), (2 : Lit), (8 : Lit)]
  , [(-3 : Lit), (4 : Lit), (8 : Lit)]
  , [(-3 : Lit), (6 : Lit), (7 : Lit)]
  , [(-3 : Lit), (6 : Lit), (8 : Lit)]
  , [(-3 : Lit), (7 : Lit), (8 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-2 : Lit), (5 : Lit), (7 : Lit)]
  , [(-1 : Lit), (2 : Lit), (4 : Lit)]
  , [(-1 : Lit), (3 : Lit), (4 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(-1 : Lit), (4 : Lit), (6 : Lit)]
  , [(-1 : Lit), (4 : Lit), (8 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(1 : Lit), (2 : Lit), (8 : Lit)]
  , [(2 : Lit), (3 : Lit), (4 : Lit)]
  , [(2 : Lit), (4 : Lit), (8 : Lit)]
  ]

def samp8GPivots : List Lit := [-10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

def samp8GVres : List Nat := [2, 4, 5, 6, 7, 8]

theorem samp8GVres_eq_samp : samp8GVres = samp8Vres := by native_decide

def samp8GClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem samp8G_closed_bool : samp8GClosedUnder samp8GClosed 3 samp8GPivots = true := by
  native_decide

theorem samp8G_lits_in_pivots :
    (samp8GClosed.all fun C => C.all fun lit => decide (lit ∈ samp8GPivots)) = true := by
  native_decide

theorem samp8G_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ samp8GClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ samp8GPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp samp8G_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem samp8G_mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : samp8GClosedUnder S w pivots = true)
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

def samp8GClosure : WidthClosure 3 where
  axioms := samp8GAxioms
  mem := fun C => C ∈ samp8GClosed
  axiom_mem := by
    intro C hC _
    have h : (samp8GAxioms.all fun A => samp8GClosed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact samp8G_mem_of_closed samp8G_closed_bool hC hD hRes hw (samp8G_pivot hC hRes)

theorem samp8G_no_empty : ¬ samp8GClosure.mem [] := by
  simp [samp8GClosure]
  native_decide

def samp8GProjOK : Bool :=
  samp8GClosed.all fun C =>
    !(supportedOn C samp8Vres) || samp8RClosed.contains C

theorem samp8GProjOK_true : samp8GProjOK = true := by native_decide

theorem samp8G_supported_in_R
    {C : Clause} (hG : C ∈ samp8GClosed) (hsup : supportedOn C samp8Vres = true) :
    C ∈ samp8RClosed := by
  have hall := (List.all_eq_true.mp samp8GProjOK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

def samp8GProjection : ProjectionInclusion 3 where
  gClosure := samp8GClosure
  rClosure := samp8RClosure
  Vres := samp8Vres
  holds := fun _ hG hsup => samp8G_supported_in_R hG hsup

def samp8GEliminationStep : EliminationStep 3 where
  before := samp8GClosure
  after := samp8RClosure
  V_after := samp8Vres
  preserves := fun _ hB hsup => samp8G_supported_in_R hB hsup

theorem samp8G_no_empty_of_projection :
    ¬ samp8GProjection.gClosure.mem [] :=
  no_empty_of_projection samp8GProjection samp8_closure_no_empty

theorem samp8_global_edge_iso_to_residualAxioms (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp8TopologyRename samp8RClosed = true ∧
      residualAxioms e = k4Axioms := by
  refine ⟨?_, residualAxioms_eq_k4 e⟩
  have h := samp8TopologySetEq_true
  simpa [topologySetEq, samp8TopologySetEq] using h

theorem samp8_fresh_g0_projects (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp8TopologyRename samp8RClosed = true ∧
      residualAxioms e = k4Axioms ∧
      ¬ samp8GProjection.gClosure.mem [] :=
  ⟨(samp8_global_edge_iso_to_residualAxioms e).1,
    (samp8_global_edge_iso_to_residualAxioms e).2,
    samp8G_no_empty_of_projection⟩

def samp8GDoc : String :=
  "fresh G₀ Closure₃ for samp8; ProjectionInclusion beyond packs/alts"

end PNPLab.Resolution
