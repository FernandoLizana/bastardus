/-
  Fresh G₀→R for hop-3 sample samp19: C_7 + chords [0, 2],[1, 6].

  Machine fact: Closure₃(G) has size 172 and excludes □; residual
  `samp19RClosed` (16) excludes □; every Closure₃(G) clause supported on
  residual edge vars lies in `samp19RClosed`.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures
import PNPLab.SampleResidualClosures

namespace PNPLab.Resolution

def samp19GAxioms : List Clause :=
  [ [(-9 : Lit), (8 : Lit)]
  , [(-8 : Lit), (7 : Lit)]
  , [(-8 : Lit), (9 : Lit)]
  , [(-7 : Lit), (6 : Lit)]
  , [(-7 : Lit), (8 : Lit)]
  , [(-6 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-9 : Lit), (3 : Lit), (5 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-6 : Lit), (2 : Lit), (4 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (3 : Lit), (9 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (2 : Lit), (6 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (5 : Lit), (9 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (4 : Lit), (6 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def samp19GClosed : List Clause :=
  [ [(-9 : Lit), (6 : Lit)]
  , [(-9 : Lit), (7 : Lit)]
  , [(-9 : Lit), (8 : Lit)]
  , [(-8 : Lit), (6 : Lit)]
  , [(-8 : Lit), (7 : Lit)]
  , [(-8 : Lit), (9 : Lit)]
  , [(-7 : Lit), (6 : Lit)]
  , [(-7 : Lit), (8 : Lit)]
  , [(-7 : Lit), (9 : Lit)]
  , [(-6 : Lit), (7 : Lit)]
  , [(-6 : Lit), (8 : Lit)]
  , [(-6 : Lit), (9 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (6 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (6 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (6 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-9 : Lit), (-4 : Lit), (6 : Lit)]
  , [(-9 : Lit), (-4 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-4 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (6 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (6 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-9 : Lit), (2 : Lit), (4 : Lit)]
  , [(-9 : Lit), (2 : Lit), (6 : Lit)]
  , [(-9 : Lit), (2 : Lit), (7 : Lit)]
  , [(-9 : Lit), (2 : Lit), (8 : Lit)]
  , [(-9 : Lit), (3 : Lit), (5 : Lit)]
  , [(-9 : Lit), (3 : Lit), (6 : Lit)]
  , [(-9 : Lit), (3 : Lit), (7 : Lit)]
  , [(-9 : Lit), (3 : Lit), (8 : Lit)]
  , [(-9 : Lit), (4 : Lit), (6 : Lit)]
  , [(-9 : Lit), (4 : Lit), (7 : Lit)]
  , [(-9 : Lit), (4 : Lit), (8 : Lit)]
  , [(-9 : Lit), (5 : Lit), (6 : Lit)]
  , [(-9 : Lit), (5 : Lit), (7 : Lit)]
  , [(-9 : Lit), (5 : Lit), (8 : Lit)]
  , [(-9 : Lit), (6 : Lit), (7 : Lit)]
  , [(-9 : Lit), (6 : Lit), (8 : Lit)]
  , [(-9 : Lit), (7 : Lit), (8 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (6 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (6 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (-4 : Lit), (6 : Lit)]
  , [(-8 : Lit), (-4 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-4 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (6 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (6 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-8 : Lit), (2 : Lit), (4 : Lit)]
  , [(-8 : Lit), (2 : Lit), (6 : Lit)]
  , [(-8 : Lit), (2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (2 : Lit), (9 : Lit)]
  , [(-8 : Lit), (3 : Lit), (5 : Lit)]
  , [(-8 : Lit), (3 : Lit), (6 : Lit)]
  , [(-8 : Lit), (3 : Lit), (7 : Lit)]
  , [(-8 : Lit), (3 : Lit), (9 : Lit)]
  , [(-8 : Lit), (4 : Lit), (6 : Lit)]
  , [(-8 : Lit), (4 : Lit), (7 : Lit)]
  , [(-8 : Lit), (4 : Lit), (9 : Lit)]
  , [(-8 : Lit), (5 : Lit), (6 : Lit)]
  , [(-8 : Lit), (5 : Lit), (7 : Lit)]
  , [(-8 : Lit), (5 : Lit), (9 : Lit)]
  , [(-8 : Lit), (6 : Lit), (7 : Lit)]
  , [(-8 : Lit), (6 : Lit), (9 : Lit)]
  , [(-8 : Lit), (7 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-7 : Lit), (2 : Lit), (4 : Lit)]
  , [(-7 : Lit), (2 : Lit), (6 : Lit)]
  , [(-7 : Lit), (2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (2 : Lit), (9 : Lit)]
  , [(-7 : Lit), (3 : Lit), (5 : Lit)]
  , [(-7 : Lit), (3 : Lit), (6 : Lit)]
  , [(-7 : Lit), (3 : Lit), (8 : Lit)]
  , [(-7 : Lit), (3 : Lit), (9 : Lit)]
  , [(-7 : Lit), (4 : Lit), (6 : Lit)]
  , [(-7 : Lit), (4 : Lit), (8 : Lit)]
  , [(-7 : Lit), (4 : Lit), (9 : Lit)]
  , [(-7 : Lit), (5 : Lit), (6 : Lit)]
  , [(-7 : Lit), (5 : Lit), (8 : Lit)]
  , [(-7 : Lit), (5 : Lit), (9 : Lit)]
  , [(-7 : Lit), (6 : Lit), (8 : Lit)]
  , [(-7 : Lit), (6 : Lit), (9 : Lit)]
  , [(-7 : Lit), (8 : Lit), (9 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (9 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (9 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-6 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-6 : Lit), (2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (2 : Lit), (7 : Lit)]
  , [(-6 : Lit), (2 : Lit), (8 : Lit)]
  , [(-6 : Lit), (2 : Lit), (9 : Lit)]
  , [(-6 : Lit), (3 : Lit), (5 : Lit)]
  , [(-6 : Lit), (3 : Lit), (7 : Lit)]
  , [(-6 : Lit), (3 : Lit), (8 : Lit)]
  , [(-6 : Lit), (3 : Lit), (9 : Lit)]
  , [(-6 : Lit), (4 : Lit), (7 : Lit)]
  , [(-6 : Lit), (4 : Lit), (8 : Lit)]
  , [(-6 : Lit), (4 : Lit), (9 : Lit)]
  , [(-6 : Lit), (5 : Lit), (7 : Lit)]
  , [(-6 : Lit), (5 : Lit), (8 : Lit)]
  , [(-6 : Lit), (5 : Lit), (9 : Lit)]
  , [(-6 : Lit), (7 : Lit), (8 : Lit)]
  , [(-6 : Lit), (7 : Lit), (9 : Lit)]
  , [(-6 : Lit), (8 : Lit), (9 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (3 : Lit), (6 : Lit)]
  , [(-5 : Lit), (3 : Lit), (7 : Lit)]
  , [(-5 : Lit), (3 : Lit), (8 : Lit)]
  , [(-5 : Lit), (3 : Lit), (9 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (2 : Lit), (6 : Lit)]
  , [(-4 : Lit), (2 : Lit), (7 : Lit)]
  , [(-4 : Lit), (2 : Lit), (8 : Lit)]
  , [(-4 : Lit), (2 : Lit), (9 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (5 : Lit), (6 : Lit)]
  , [(-3 : Lit), (5 : Lit), (7 : Lit)]
  , [(-3 : Lit), (5 : Lit), (8 : Lit)]
  , [(-3 : Lit), (5 : Lit), (9 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (4 : Lit), (6 : Lit)]
  , [(-2 : Lit), (4 : Lit), (7 : Lit)]
  , [(-2 : Lit), (4 : Lit), (8 : Lit)]
  , [(-2 : Lit), (4 : Lit), (9 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def samp19GPivots : List Lit := [-11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

def samp19GVres : List Nat := [1, 2, 3, 4, 5, 7]

theorem samp19GVres_eq_samp : samp19GVres = samp19Vres := by native_decide

def samp19GClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem samp19G_closed_bool : samp19GClosedUnder samp19GClosed 3 samp19GPivots = true := by
  native_decide

theorem samp19G_lits_in_pivots :
    (samp19GClosed.all fun C => C.all fun lit => decide (lit ∈ samp19GPivots)) = true := by
  native_decide

theorem samp19G_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ samp19GClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ samp19GPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp samp19G_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem samp19G_mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : samp19GClosedUnder S w pivots = true)
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

def samp19GClosure : WidthClosure 3 where
  axioms := samp19GAxioms
  mem := fun C => C ∈ samp19GClosed
  axiom_mem := by
    intro C hC _
    have h : (samp19GAxioms.all fun A => samp19GClosed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact samp19G_mem_of_closed samp19G_closed_bool hC hD hRes hw (samp19G_pivot hC hRes)

theorem samp19G_no_empty : ¬ samp19GClosure.mem [] := by
  simp [samp19GClosure]
  native_decide

def samp19GProjOK : Bool :=
  samp19GClosed.all fun C =>
    !(supportedOn C samp19Vres) || samp19RClosed.contains C

theorem samp19GProjOK_true : samp19GProjOK = true := by native_decide

theorem samp19G_supported_in_R
    {C : Clause} (hG : C ∈ samp19GClosed) (hsup : supportedOn C samp19Vres = true) :
    C ∈ samp19RClosed := by
  have hall := (List.all_eq_true.mp samp19GProjOK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

def samp19GProjection : ProjectionInclusion 3 where
  gClosure := samp19GClosure
  rClosure := samp19RClosure
  Vres := samp19Vres
  holds := fun _ hG hsup => samp19G_supported_in_R hG hsup

def samp19GEliminationStep : EliminationStep 3 where
  before := samp19GClosure
  after := samp19RClosure
  V_after := samp19Vres
  preserves := fun _ hB hsup => samp19G_supported_in_R hB hsup

theorem samp19G_no_empty_of_projection :
    ¬ samp19GProjection.gClosure.mem [] :=
  no_empty_of_projection samp19GProjection samp19_closure_no_empty

theorem samp19_global_edge_iso_to_residualAxioms (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp19TopologyRename samp19RClosed = true ∧
      residualAxioms e = k4Axioms := by
  refine ⟨?_, residualAxioms_eq_k4 e⟩
  have h := samp19TopologySetEq_true
  simpa [topologySetEq, samp19TopologySetEq] using h

theorem samp19_fresh_g0_projects (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp19TopologyRename samp19RClosed = true ∧
      residualAxioms e = k4Axioms ∧
      ¬ samp19GProjection.gClosure.mem [] :=
  ⟨(samp19_global_edge_iso_to_residualAxioms e).1,
    (samp19_global_edge_iso_to_residualAxioms e).2,
    samp19G_no_empty_of_projection⟩

def samp19GDoc : String :=
  "fresh G₀ Closure₃ for samp19; ProjectionInclusion beyond packs/alts"

end PNPLab.Resolution
