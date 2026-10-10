/-
  Fresh G₀→R for hop-3 sample samp31: C_7 + chords [0, 5],[1, 6].

  Machine fact: Closure₃(G) has size 172 and excludes □; residual
  `samp31RClosed` (16) excludes □; every Closure₃(G) clause supported on
  residual edge vars lies in `samp31RClosed`.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures
import PNPLab.SampleResidualClosures

namespace PNPLab.Resolution

def samp31GAxioms : List Clause :=
  [ [(-8 : Lit), (7 : Lit)]
  , [(-7 : Lit), (6 : Lit)]
  , [(-7 : Lit), (8 : Lit)]
  , [(-6 : Lit), (4 : Lit)]
  , [(-6 : Lit), (7 : Lit)]
  , [(-4 : Lit), (6 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (-2 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-9 : Lit), (2 : Lit), (8 : Lit)]
  , [(-9 : Lit), (3 : Lit), (5 : Lit)]
  , [(-8 : Lit), (2 : Lit), (9 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (3 : Lit), (9 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (5 : Lit), (9 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (8 : Lit), (9 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def samp31GClosed : List Clause :=
  [ [(-8 : Lit), (4 : Lit)]
  , [(-8 : Lit), (6 : Lit)]
  , [(-8 : Lit), (7 : Lit)]
  , [(-7 : Lit), (4 : Lit)]
  , [(-7 : Lit), (6 : Lit)]
  , [(-7 : Lit), (8 : Lit)]
  , [(-6 : Lit), (4 : Lit)]
  , [(-6 : Lit), (7 : Lit)]
  , [(-6 : Lit), (8 : Lit)]
  , [(-4 : Lit), (6 : Lit)]
  , [(-4 : Lit), (7 : Lit)]
  , [(-4 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (-2 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (4 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (6 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (-2 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (4 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (6 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (4 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-9 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-9 : Lit), (-4 : Lit), (6 : Lit)]
  , [(-9 : Lit), (-4 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-4 : Lit), (8 : Lit)]
  , [(-9 : Lit), (2 : Lit), (4 : Lit)]
  , [(-9 : Lit), (2 : Lit), (6 : Lit)]
  , [(-9 : Lit), (2 : Lit), (7 : Lit)]
  , [(-9 : Lit), (2 : Lit), (8 : Lit)]
  , [(-9 : Lit), (3 : Lit), (5 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (4 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (6 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (4 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (4 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (6 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-4 : Lit), (6 : Lit)]
  , [(-8 : Lit), (-4 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (6 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (6 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-8 : Lit), (1 : Lit), (4 : Lit)]
  , [(-8 : Lit), (1 : Lit), (5 : Lit)]
  , [(-8 : Lit), (1 : Lit), (6 : Lit)]
  , [(-8 : Lit), (1 : Lit), (7 : Lit)]
  , [(-8 : Lit), (2 : Lit), (4 : Lit)]
  , [(-8 : Lit), (2 : Lit), (6 : Lit)]
  , [(-8 : Lit), (2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (2 : Lit), (9 : Lit)]
  , [(-8 : Lit), (4 : Lit), (5 : Lit)]
  , [(-8 : Lit), (4 : Lit), (6 : Lit)]
  , [(-8 : Lit), (4 : Lit), (7 : Lit)]
  , [(-8 : Lit), (4 : Lit), (9 : Lit)]
  , [(-8 : Lit), (5 : Lit), (6 : Lit)]
  , [(-8 : Lit), (5 : Lit), (7 : Lit)]
  , [(-8 : Lit), (6 : Lit), (7 : Lit)]
  , [(-8 : Lit), (6 : Lit), (9 : Lit)]
  , [(-8 : Lit), (7 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (4 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (4 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-7 : Lit), (1 : Lit), (4 : Lit)]
  , [(-7 : Lit), (1 : Lit), (5 : Lit)]
  , [(-7 : Lit), (1 : Lit), (6 : Lit)]
  , [(-7 : Lit), (1 : Lit), (8 : Lit)]
  , [(-7 : Lit), (2 : Lit), (4 : Lit)]
  , [(-7 : Lit), (2 : Lit), (6 : Lit)]
  , [(-7 : Lit), (2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (2 : Lit), (9 : Lit)]
  , [(-7 : Lit), (4 : Lit), (5 : Lit)]
  , [(-7 : Lit), (4 : Lit), (6 : Lit)]
  , [(-7 : Lit), (4 : Lit), (8 : Lit)]
  , [(-7 : Lit), (4 : Lit), (9 : Lit)]
  , [(-7 : Lit), (5 : Lit), (6 : Lit)]
  , [(-7 : Lit), (5 : Lit), (8 : Lit)]
  , [(-7 : Lit), (6 : Lit), (8 : Lit)]
  , [(-7 : Lit), (6 : Lit), (9 : Lit)]
  , [(-7 : Lit), (8 : Lit), (9 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (4 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-6 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-6 : Lit), (1 : Lit), (4 : Lit)]
  , [(-6 : Lit), (1 : Lit), (5 : Lit)]
  , [(-6 : Lit), (1 : Lit), (7 : Lit)]
  , [(-6 : Lit), (1 : Lit), (8 : Lit)]
  , [(-6 : Lit), (2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (2 : Lit), (7 : Lit)]
  , [(-6 : Lit), (2 : Lit), (8 : Lit)]
  , [(-6 : Lit), (2 : Lit), (9 : Lit)]
  , [(-6 : Lit), (4 : Lit), (5 : Lit)]
  , [(-6 : Lit), (4 : Lit), (7 : Lit)]
  , [(-6 : Lit), (4 : Lit), (8 : Lit)]
  , [(-6 : Lit), (4 : Lit), (9 : Lit)]
  , [(-6 : Lit), (5 : Lit), (7 : Lit)]
  , [(-6 : Lit), (5 : Lit), (8 : Lit)]
  , [(-6 : Lit), (7 : Lit), (8 : Lit)]
  , [(-6 : Lit), (7 : Lit), (9 : Lit)]
  , [(-6 : Lit), (8 : Lit), (9 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (6 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (7 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (8 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (1 : Lit), (7 : Lit)]
  , [(-5 : Lit), (1 : Lit), (8 : Lit)]
  , [(-5 : Lit), (3 : Lit), (9 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (6 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (6 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (1 : Lit), (6 : Lit)]
  , [(-4 : Lit), (1 : Lit), (7 : Lit)]
  , [(-4 : Lit), (1 : Lit), (8 : Lit)]
  , [(-4 : Lit), (2 : Lit), (6 : Lit)]
  , [(-4 : Lit), (2 : Lit), (7 : Lit)]
  , [(-4 : Lit), (2 : Lit), (8 : Lit)]
  , [(-4 : Lit), (2 : Lit), (9 : Lit)]
  , [(-4 : Lit), (5 : Lit), (6 : Lit)]
  , [(-4 : Lit), (5 : Lit), (7 : Lit)]
  , [(-4 : Lit), (5 : Lit), (8 : Lit)]
  , [(-4 : Lit), (6 : Lit), (7 : Lit)]
  , [(-4 : Lit), (6 : Lit), (8 : Lit)]
  , [(-4 : Lit), (6 : Lit), (9 : Lit)]
  , [(-4 : Lit), (7 : Lit), (8 : Lit)]
  , [(-4 : Lit), (7 : Lit), (9 : Lit)]
  , [(-4 : Lit), (8 : Lit), (9 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (5 : Lit), (9 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (4 : Lit), (9 : Lit)]
  , [(-2 : Lit), (6 : Lit), (9 : Lit)]
  , [(-2 : Lit), (7 : Lit), (9 : Lit)]
  , [(-2 : Lit), (8 : Lit), (9 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(-1 : Lit), (5 : Lit), (7 : Lit)]
  , [(-1 : Lit), (5 : Lit), (8 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def samp31GPivots : List Lit := [-11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

def samp31GVres : List Nat := [1, 2, 3, 5, 6, 9]

theorem samp31GVres_eq_samp : samp31GVres = samp31Vres := by native_decide

def samp31GClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem samp31G_closed_bool : samp31GClosedUnder samp31GClosed 3 samp31GPivots = true := by
  native_decide

theorem samp31G_lits_in_pivots :
    (samp31GClosed.all fun C => C.all fun lit => decide (lit ∈ samp31GPivots)) = true := by
  native_decide

theorem samp31G_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ samp31GClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ samp31GPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp samp31G_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem samp31G_mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : samp31GClosedUnder S w pivots = true)
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

def samp31GClosure : WidthClosure 3 where
  axioms := samp31GAxioms
  mem := fun C => C ∈ samp31GClosed
  axiom_mem := by
    intro C hC _
    have h : (samp31GAxioms.all fun A => samp31GClosed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact samp31G_mem_of_closed samp31G_closed_bool hC hD hRes hw (samp31G_pivot hC hRes)

theorem samp31G_no_empty : ¬ samp31GClosure.mem [] := by
  simp [samp31GClosure]
  native_decide

def samp31GProjOK : Bool :=
  samp31GClosed.all fun C =>
    !(supportedOn C samp31Vres) || samp31RClosed.contains C

theorem samp31GProjOK_true : samp31GProjOK = true := by native_decide

theorem samp31G_supported_in_R
    {C : Clause} (hG : C ∈ samp31GClosed) (hsup : supportedOn C samp31Vres = true) :
    C ∈ samp31RClosed := by
  have hall := (List.all_eq_true.mp samp31GProjOK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

def samp31GProjection : ProjectionInclusion 3 where
  gClosure := samp31GClosure
  rClosure := samp31RClosure
  Vres := samp31Vres
  holds := fun _ hG hsup => samp31G_supported_in_R hG hsup

def samp31GEliminationStep : EliminationStep 3 where
  before := samp31GClosure
  after := samp31RClosure
  V_after := samp31Vres
  preserves := fun _ hB hsup => samp31G_supported_in_R hB hsup

theorem samp31G_no_empty_of_projection :
    ¬ samp31GProjection.gClosure.mem [] :=
  no_empty_of_projection samp31GProjection samp31_closure_no_empty

theorem samp31_global_edge_iso_to_residualAxioms (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp31TopologyRename samp31RClosed = true ∧
      residualAxioms e = k4Axioms := by
  refine ⟨?_, residualAxioms_eq_k4 e⟩
  have h := samp31TopologySetEq_true
  simpa [topologySetEq, samp31TopologySetEq] using h

theorem samp31_fresh_g0_projects (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp31TopologyRename samp31RClosed = true ∧
      residualAxioms e = k4Axioms ∧
      ¬ samp31GProjection.gClosure.mem [] :=
  ⟨(samp31_global_edge_iso_to_residualAxioms e).1,
    (samp31_global_edge_iso_to_residualAxioms e).2,
    samp31G_no_empty_of_projection⟩

def samp31GDoc : String :=
  "fresh G₀ Closure₃ for samp31; ProjectionInclusion beyond packs/alts"

end PNPLab.Resolution
