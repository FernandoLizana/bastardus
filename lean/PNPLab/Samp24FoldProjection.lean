/-
  Fresh G₀→R for hop-3 sample samp24: C_7 + chords [0, 3],[2, 5].

  Machine fact: Closure₃(G) has size 118 and excludes □; residual
  `samp24RClosed` (16) excludes □; every Closure₃(G) clause supported on
  residual edge vars lies in `samp24RClosed`.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures
import PNPLab.SampleResidualClosures

namespace PNPLab.Resolution

def samp24GAxioms : List Clause :=
  [ [(-9 : Lit), (3 : Lit)]
  , [(-8 : Lit), (7 : Lit)]
  , [(-7 : Lit), (8 : Lit)]
  , [(-4 : Lit), (1 : Lit)]
  , [(-3 : Lit), (9 : Lit)]
  , [(-1 : Lit), (4 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (-6 : Lit)]
  , [(-9 : Lit), (6 : Lit), (8 : Lit)]
  , [(-8 : Lit), (6 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (-2 : Lit)]
  , [(-7 : Lit), (2 : Lit), (5 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-4 : Lit)]
  , [(-6 : Lit), (4 : Lit), (5 : Lit)]
  , [(-6 : Lit), (8 : Lit), (9 : Lit)]
  , [(-5 : Lit), (2 : Lit), (7 : Lit)]
  , [(-5 : Lit), (4 : Lit), (6 : Lit)]
  , [(-4 : Lit), (5 : Lit), (6 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (5 : Lit), (7 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def samp24GClosed : List Clause :=
  [ [(-9 : Lit), (3 : Lit)]
  , [(-8 : Lit), (7 : Lit)]
  , [(-7 : Lit), (8 : Lit)]
  , [(-4 : Lit), (1 : Lit)]
  , [(-3 : Lit), (9 : Lit)]
  , [(-1 : Lit), (4 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (-6 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (-6 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-4 : Lit), (1 : Lit)]
  , [(-9 : Lit), (-4 : Lit), (2 : Lit)]
  , [(-9 : Lit), (-4 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-9 : Lit), (1 : Lit), (3 : Lit)]
  , [(-9 : Lit), (2 : Lit), (3 : Lit)]
  , [(-9 : Lit), (3 : Lit), (4 : Lit)]
  , [(-9 : Lit), (3 : Lit), (6 : Lit)]
  , [(-9 : Lit), (3 : Lit), (7 : Lit)]
  , [(-9 : Lit), (3 : Lit), (8 : Lit)]
  , [(-9 : Lit), (6 : Lit), (7 : Lit)]
  , [(-9 : Lit), (6 : Lit), (8 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-3 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (2 : Lit), (5 : Lit)]
  , [(-8 : Lit), (2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (3 : Lit), (6 : Lit)]
  , [(-8 : Lit), (3 : Lit), (7 : Lit)]
  , [(-8 : Lit), (5 : Lit), (7 : Lit)]
  , [(-8 : Lit), (6 : Lit), (7 : Lit)]
  , [(-8 : Lit), (6 : Lit), (9 : Lit)]
  , [(-8 : Lit), (7 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-3 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (-2 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (2 : Lit), (5 : Lit)]
  , [(-7 : Lit), (2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (3 : Lit), (6 : Lit)]
  , [(-7 : Lit), (3 : Lit), (8 : Lit)]
  , [(-7 : Lit), (5 : Lit), (8 : Lit)]
  , [(-7 : Lit), (6 : Lit), (8 : Lit)]
  , [(-7 : Lit), (6 : Lit), (9 : Lit)]
  , [(-7 : Lit), (8 : Lit), (9 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-4 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (1 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-6 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-6 : Lit), (1 : Lit), (5 : Lit)]
  , [(-6 : Lit), (3 : Lit), (7 : Lit)]
  , [(-6 : Lit), (3 : Lit), (8 : Lit)]
  , [(-6 : Lit), (4 : Lit), (5 : Lit)]
  , [(-6 : Lit), (7 : Lit), (9 : Lit)]
  , [(-6 : Lit), (8 : Lit), (9 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (1 : Lit)]
  , [(-5 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (2 : Lit), (7 : Lit)]
  , [(-5 : Lit), (2 : Lit), (8 : Lit)]
  , [(-5 : Lit), (4 : Lit), (6 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (1 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (2 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-4 : Lit), (1 : Lit), (2 : Lit)]
  , [(-4 : Lit), (1 : Lit), (3 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (1 : Lit), (6 : Lit)]
  , [(-4 : Lit), (1 : Lit), (9 : Lit)]
  , [(-4 : Lit), (5 : Lit), (6 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-3 : Lit), (1 : Lit), (9 : Lit)]
  , [(-3 : Lit), (2 : Lit), (9 : Lit)]
  , [(-3 : Lit), (4 : Lit), (9 : Lit)]
  , [(-3 : Lit), (6 : Lit), (7 : Lit)]
  , [(-3 : Lit), (6 : Lit), (8 : Lit)]
  , [(-3 : Lit), (6 : Lit), (9 : Lit)]
  , [(-3 : Lit), (7 : Lit), (9 : Lit)]
  , [(-3 : Lit), (8 : Lit), (9 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-2 : Lit), (5 : Lit), (7 : Lit)]
  , [(-2 : Lit), (5 : Lit), (8 : Lit)]
  , [(-1 : Lit), (2 : Lit), (4 : Lit)]
  , [(-1 : Lit), (3 : Lit), (4 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(-1 : Lit), (4 : Lit), (6 : Lit)]
  , [(-1 : Lit), (4 : Lit), (9 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(1 : Lit), (2 : Lit), (9 : Lit)]
  , [(2 : Lit), (3 : Lit), (4 : Lit)]
  , [(2 : Lit), (4 : Lit), (9 : Lit)]
  ]

def samp24GPivots : List Lit := [-11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

def samp24GVres : List Nat := [2, 4, 5, 6, 8, 9]

theorem samp24GVres_eq_samp : samp24GVres = samp24Vres := by native_decide

def samp24GClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem samp24G_closed_bool : samp24GClosedUnder samp24GClosed 3 samp24GPivots = true := by
  native_decide

theorem samp24G_lits_in_pivots :
    (samp24GClosed.all fun C => C.all fun lit => decide (lit ∈ samp24GPivots)) = true := by
  native_decide

theorem samp24G_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ samp24GClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ samp24GPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp samp24G_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem samp24G_mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : samp24GClosedUnder S w pivots = true)
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

def samp24GClosure : WidthClosure 3 where
  axioms := samp24GAxioms
  mem := fun C => C ∈ samp24GClosed
  axiom_mem := by
    intro C hC _
    have h : (samp24GAxioms.all fun A => samp24GClosed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact samp24G_mem_of_closed samp24G_closed_bool hC hD hRes hw (samp24G_pivot hC hRes)

theorem samp24G_no_empty : ¬ samp24GClosure.mem [] := by
  simp [samp24GClosure]
  native_decide

def samp24GProjOK : Bool :=
  samp24GClosed.all fun C =>
    !(supportedOn C samp24Vres) || samp24RClosed.contains C

theorem samp24GProjOK_true : samp24GProjOK = true := by native_decide

theorem samp24G_supported_in_R
    {C : Clause} (hG : C ∈ samp24GClosed) (hsup : supportedOn C samp24Vres = true) :
    C ∈ samp24RClosed := by
  have hall := (List.all_eq_true.mp samp24GProjOK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

def samp24GProjection : ProjectionInclusion 3 where
  gClosure := samp24GClosure
  rClosure := samp24RClosure
  Vres := samp24Vres
  holds := fun _ hG hsup => samp24G_supported_in_R hG hsup

def samp24GEliminationStep : EliminationStep 3 where
  before := samp24GClosure
  after := samp24RClosure
  V_after := samp24Vres
  preserves := fun _ hB hsup => samp24G_supported_in_R hB hsup

theorem samp24G_no_empty_of_projection :
    ¬ samp24GProjection.gClosure.mem [] :=
  no_empty_of_projection samp24GProjection samp24_closure_no_empty

theorem samp24_global_edge_iso_to_residualAxioms (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp24TopologyRename samp24RClosed = true ∧
      residualAxioms e = k4Axioms := by
  refine ⟨?_, residualAxioms_eq_k4 e⟩
  have h := samp24TopologySetEq_true
  simpa [topologySetEq, samp24TopologySetEq] using h

theorem samp24_fresh_g0_projects (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp24TopologyRename samp24RClosed = true ∧
      residualAxioms e = k4Axioms ∧
      ¬ samp24GProjection.gClosure.mem [] :=
  ⟨(samp24_global_edge_iso_to_residualAxioms e).1,
    (samp24_global_edge_iso_to_residualAxioms e).2,
    samp24G_no_empty_of_projection⟩

def samp24GDoc : String :=
  "fresh G₀ Closure₃ for samp24; ProjectionInclusion beyond packs/alts"

end PNPLab.Resolution
