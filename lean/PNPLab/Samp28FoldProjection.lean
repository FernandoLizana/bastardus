/-
  Fresh G₀→R for hop-3 sample samp28: C_7 + chords [0, 4],[2, 6].

  Machine fact: Closure₃(G) has size 118 and excludes □; residual
  `samp28RClosed` (16) excludes □; every Closure₃(G) clause supported on
  residual edge vars lies in `samp28RClosed`.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures
import PNPLab.SampleResidualClosures

namespace PNPLab.Resolution

def samp28GAxioms : List Clause :=
  [ [(-9 : Lit), (8 : Lit)]
  , [(-8 : Lit), (9 : Lit)]
  , [(-7 : Lit), (5 : Lit)]
  , [(-5 : Lit), (7 : Lit)]
  , [(-4 : Lit), (1 : Lit)]
  , [(-1 : Lit), (4 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (-3 : Lit)]
  , [(-9 : Lit), (3 : Lit), (6 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (2 : Lit), (7 : Lit)]
  , [(-7 : Lit), (2 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-4 : Lit)]
  , [(-6 : Lit), (3 : Lit), (9 : Lit)]
  , [(-6 : Lit), (4 : Lit), (5 : Lit)]
  , [(-5 : Lit), (4 : Lit), (6 : Lit)]
  , [(-4 : Lit), (5 : Lit), (6 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (6 : Lit), (9 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (7 : Lit), (8 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def samp28GClosed : List Clause :=
  [ [(-9 : Lit), (8 : Lit)]
  , [(-8 : Lit), (9 : Lit)]
  , [(-7 : Lit), (5 : Lit)]
  , [(-5 : Lit), (7 : Lit)]
  , [(-4 : Lit), (1 : Lit)]
  , [(-1 : Lit), (4 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (-2 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (5 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (-3 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (-2 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-9 : Lit), (2 : Lit), (5 : Lit)]
  , [(-9 : Lit), (2 : Lit), (7 : Lit)]
  , [(-9 : Lit), (2 : Lit), (8 : Lit)]
  , [(-9 : Lit), (3 : Lit), (6 : Lit)]
  , [(-9 : Lit), (3 : Lit), (8 : Lit)]
  , [(-9 : Lit), (5 : Lit), (8 : Lit)]
  , [(-9 : Lit), (6 : Lit), (8 : Lit)]
  , [(-9 : Lit), (7 : Lit), (8 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (5 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-3 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-8 : Lit), (2 : Lit), (5 : Lit)]
  , [(-8 : Lit), (2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (2 : Lit), (9 : Lit)]
  , [(-8 : Lit), (3 : Lit), (6 : Lit)]
  , [(-8 : Lit), (3 : Lit), (9 : Lit)]
  , [(-8 : Lit), (5 : Lit), (9 : Lit)]
  , [(-8 : Lit), (6 : Lit), (9 : Lit)]
  , [(-8 : Lit), (7 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-4 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-1 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (5 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (1 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (5 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (5 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (5 : Lit)]
  , [(-7 : Lit), (1 : Lit), (5 : Lit)]
  , [(-7 : Lit), (1 : Lit), (6 : Lit)]
  , [(-7 : Lit), (2 : Lit), (5 : Lit)]
  , [(-7 : Lit), (2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (2 : Lit), (9 : Lit)]
  , [(-7 : Lit), (4 : Lit), (5 : Lit)]
  , [(-7 : Lit), (4 : Lit), (6 : Lit)]
  , [(-7 : Lit), (5 : Lit), (6 : Lit)]
  , [(-7 : Lit), (5 : Lit), (8 : Lit)]
  , [(-7 : Lit), (5 : Lit), (9 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-4 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (1 : Lit)]
  , [(-6 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-6 : Lit), (1 : Lit), (5 : Lit)]
  , [(-6 : Lit), (1 : Lit), (7 : Lit)]
  , [(-6 : Lit), (3 : Lit), (8 : Lit)]
  , [(-6 : Lit), (3 : Lit), (9 : Lit)]
  , [(-6 : Lit), (4 : Lit), (5 : Lit)]
  , [(-6 : Lit), (4 : Lit), (7 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (1 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (7 : Lit)]
  , [(-5 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-5 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (1 : Lit), (7 : Lit)]
  , [(-5 : Lit), (2 : Lit), (7 : Lit)]
  , [(-5 : Lit), (2 : Lit), (8 : Lit)]
  , [(-5 : Lit), (2 : Lit), (9 : Lit)]
  , [(-5 : Lit), (4 : Lit), (6 : Lit)]
  , [(-5 : Lit), (4 : Lit), (7 : Lit)]
  , [(-5 : Lit), (6 : Lit), (7 : Lit)]
  , [(-5 : Lit), (7 : Lit), (8 : Lit)]
  , [(-5 : Lit), (7 : Lit), (9 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (1 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (2 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-4 : Lit), (1 : Lit), (2 : Lit)]
  , [(-4 : Lit), (1 : Lit), (3 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (1 : Lit), (6 : Lit)]
  , [(-4 : Lit), (1 : Lit), (7 : Lit)]
  , [(-4 : Lit), (5 : Lit), (6 : Lit)]
  , [(-4 : Lit), (6 : Lit), (7 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-3 : Lit), (6 : Lit), (8 : Lit)]
  , [(-3 : Lit), (6 : Lit), (9 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-2 : Lit), (5 : Lit), (8 : Lit)]
  , [(-2 : Lit), (5 : Lit), (9 : Lit)]
  , [(-2 : Lit), (7 : Lit), (8 : Lit)]
  , [(-2 : Lit), (7 : Lit), (9 : Lit)]
  , [(-1 : Lit), (2 : Lit), (4 : Lit)]
  , [(-1 : Lit), (3 : Lit), (4 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(-1 : Lit), (4 : Lit), (6 : Lit)]
  , [(-1 : Lit), (4 : Lit), (7 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(-1 : Lit), (6 : Lit), (7 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(2 : Lit), (3 : Lit), (4 : Lit)]
  ]

def samp28GPivots : List Lit := [-11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

def samp28GVres : List Nat := [2, 3, 4, 6, 7, 9]

theorem samp28GVres_eq_samp : samp28GVres = samp28Vres := by native_decide

def samp28GClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem samp28G_closed_bool : samp28GClosedUnder samp28GClosed 3 samp28GPivots = true := by
  native_decide

theorem samp28G_lits_in_pivots :
    (samp28GClosed.all fun C => C.all fun lit => decide (lit ∈ samp28GPivots)) = true := by
  native_decide

theorem samp28G_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ samp28GClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ samp28GPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp samp28G_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem samp28G_mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : samp28GClosedUnder S w pivots = true)
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

def samp28GClosure : WidthClosure 3 where
  axioms := samp28GAxioms
  mem := fun C => C ∈ samp28GClosed
  axiom_mem := by
    intro C hC _
    have h : (samp28GAxioms.all fun A => samp28GClosed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact samp28G_mem_of_closed samp28G_closed_bool hC hD hRes hw (samp28G_pivot hC hRes)

theorem samp28G_no_empty : ¬ samp28GClosure.mem [] := by
  simp [samp28GClosure]
  native_decide

def samp28GProjOK : Bool :=
  samp28GClosed.all fun C =>
    !(supportedOn C samp28Vres) || samp28RClosed.contains C

theorem samp28GProjOK_true : samp28GProjOK = true := by native_decide

theorem samp28G_supported_in_R
    {C : Clause} (hG : C ∈ samp28GClosed) (hsup : supportedOn C samp28Vres = true) :
    C ∈ samp28RClosed := by
  have hall := (List.all_eq_true.mp samp28GProjOK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

def samp28GProjection : ProjectionInclusion 3 where
  gClosure := samp28GClosure
  rClosure := samp28RClosure
  Vres := samp28Vres
  holds := fun _ hG hsup => samp28G_supported_in_R hG hsup

def samp28GEliminationStep : EliminationStep 3 where
  before := samp28GClosure
  after := samp28RClosure
  V_after := samp28Vres
  preserves := fun _ hB hsup => samp28G_supported_in_R hB hsup

theorem samp28G_no_empty_of_projection :
    ¬ samp28GProjection.gClosure.mem [] :=
  no_empty_of_projection samp28GProjection samp28_closure_no_empty

theorem samp28_global_edge_iso_to_residualAxioms (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp28TopologyRename samp28RClosed = true ∧
      residualAxioms e = k4Axioms := by
  refine ⟨?_, residualAxioms_eq_k4 e⟩
  have h := samp28TopologySetEq_true
  simpa [topologySetEq, samp28TopologySetEq] using h

theorem samp28_fresh_g0_projects (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp28TopologyRename samp28RClosed = true ∧
      residualAxioms e = k4Axioms ∧
      ¬ samp28GProjection.gClosure.mem [] :=
  ⟨(samp28_global_edge_iso_to_residualAxioms e).1,
    (samp28_global_edge_iso_to_residualAxioms e).2,
    samp28G_no_empty_of_projection⟩

def samp28GDoc : String :=
  "fresh G₀ Closure₃ for samp28; ProjectionInclusion beyond packs/alts"

end PNPLab.Resolution
