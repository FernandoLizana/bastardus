/-
  Fresh G₀→R for hop-1 sample samp2: C_5 + chords [0, 3],[2, 4].

  Machine fact: Closure₃(G) has size 42 and excludes □; residual
  `samp2RClosed` (16) excludes □; every Closure₃(G) clause supported on
  residual edge vars lies in `samp2RClosed`.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures
import PNPLab.SampleResidualClosures

namespace PNPLab.Resolution

def samp2GAxioms : List Clause :=
  [ [(-4 : Lit), (1 : Lit)]
  , [(-1 : Lit), (4 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-3 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (-2 : Lit)]
  , [(-7 : Lit), (2 : Lit), (5 : Lit)]
  , [(-7 : Lit), (3 : Lit), (6 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-4 : Lit)]
  , [(-6 : Lit), (3 : Lit), (7 : Lit)]
  , [(-6 : Lit), (4 : Lit), (5 : Lit)]
  , [(-5 : Lit), (2 : Lit), (7 : Lit)]
  , [(-5 : Lit), (4 : Lit), (6 : Lit)]
  , [(-4 : Lit), (5 : Lit), (6 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (6 : Lit), (7 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (5 : Lit), (7 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def samp2GClosed : List Clause :=
  [ [(-4 : Lit), (1 : Lit)]
  , [(-1 : Lit), (4 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-3 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (-2 : Lit)]
  , [(-7 : Lit), (2 : Lit), (5 : Lit)]
  , [(-7 : Lit), (3 : Lit), (6 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-4 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (1 : Lit)]
  , [(-6 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-6 : Lit), (1 : Lit), (5 : Lit)]
  , [(-6 : Lit), (3 : Lit), (7 : Lit)]
  , [(-6 : Lit), (4 : Lit), (5 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (1 : Lit)]
  , [(-5 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (2 : Lit), (7 : Lit)]
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
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-2 : Lit), (5 : Lit), (7 : Lit)]
  , [(-1 : Lit), (2 : Lit), (4 : Lit)]
  , [(-1 : Lit), (3 : Lit), (4 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(-1 : Lit), (4 : Lit), (6 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(2 : Lit), (3 : Lit), (4 : Lit)]
  ]

def samp2GPivots : List Lit := [-10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

def samp2GVres : List Nat := [2, 3, 4, 5, 6, 7]

theorem samp2GVres_eq_samp : samp2GVres = samp2Vres := by native_decide

def samp2GClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem samp2G_closed_bool : samp2GClosedUnder samp2GClosed 3 samp2GPivots = true := by
  native_decide

theorem samp2G_lits_in_pivots :
    (samp2GClosed.all fun C => C.all fun lit => decide (lit ∈ samp2GPivots)) = true := by
  native_decide

theorem samp2G_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ samp2GClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ samp2GPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp samp2G_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem samp2G_mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : samp2GClosedUnder S w pivots = true)
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

def samp2GClosure : WidthClosure 3 where
  axioms := samp2GAxioms
  mem := fun C => C ∈ samp2GClosed
  axiom_mem := by
    intro C hC _
    have h : (samp2GAxioms.all fun A => samp2GClosed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact samp2G_mem_of_closed samp2G_closed_bool hC hD hRes hw (samp2G_pivot hC hRes)

theorem samp2G_no_empty : ¬ samp2GClosure.mem [] := by
  simp [samp2GClosure]
  native_decide

def samp2GProjOK : Bool :=
  samp2GClosed.all fun C =>
    !(supportedOn C samp2Vres) || samp2RClosed.contains C

theorem samp2GProjOK_true : samp2GProjOK = true := by native_decide

theorem samp2G_supported_in_R
    {C : Clause} (hG : C ∈ samp2GClosed) (hsup : supportedOn C samp2Vres = true) :
    C ∈ samp2RClosed := by
  have hall := (List.all_eq_true.mp samp2GProjOK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

def samp2GProjection : ProjectionInclusion 3 where
  gClosure := samp2GClosure
  rClosure := samp2RClosure
  Vres := samp2Vres
  holds := fun _ hG hsup => samp2G_supported_in_R hG hsup

def samp2GEliminationStep : EliminationStep 3 where
  before := samp2GClosure
  after := samp2RClosure
  V_after := samp2Vres
  preserves := fun _ hB hsup => samp2G_supported_in_R hB hsup

theorem samp2G_no_empty_of_projection :
    ¬ samp2GProjection.gClosure.mem [] :=
  no_empty_of_projection samp2GProjection samp2_closure_no_empty

theorem samp2_global_edge_iso_to_residualAxioms (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp2TopologyRename samp2RClosed = true ∧
      residualAxioms e = k4Axioms := by
  refine ⟨?_, residualAxioms_eq_k4 e⟩
  have h := samp2TopologySetEq_true
  simpa [topologySetEq, samp2TopologySetEq] using h

theorem samp2_fresh_g0_projects (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp2TopologyRename samp2RClosed = true ∧
      residualAxioms e = k4Axioms ∧
      ¬ samp2GProjection.gClosure.mem [] :=
  ⟨(samp2_global_edge_iso_to_residualAxioms e).1,
    (samp2_global_edge_iso_to_residualAxioms e).2,
    samp2G_no_empty_of_projection⟩

def samp2GDoc : String :=
  "fresh G₀ Closure₃ for samp2; ProjectionInclusion beyond packs/alts"

end PNPLab.Resolution
