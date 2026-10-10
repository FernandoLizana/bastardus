/-
  Fresh G₀→R for hop-2 sample samp16: C_6 + chords [2, 4],[3, 5].

  Machine fact: Closure₃(G) has size 92 and excludes □; residual
  `samp16RClosed` (16) excludes □; every Closure₃(G) clause supported on
  residual edge vars lies in `samp16RClosed`.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures
import PNPLab.SampleResidualClosures

namespace PNPLab.Resolution

def samp16GAxioms : List Clause :=
  [ [(-3 : Lit), (1 : Lit)]
  , [(-2 : Lit), (1 : Lit)]
  , [(-1 : Lit), (2 : Lit)]
  , [(-1 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-8 : Lit), (2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (5 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-4 : Lit)]
  , [(-7 : Lit), (2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (4 : Lit), (6 : Lit)]
  , [(-6 : Lit), (4 : Lit), (7 : Lit)]
  , [(-6 : Lit), (5 : Lit), (8 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (3 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (4 : Lit)]
  , [(-5 : Lit), (6 : Lit), (8 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (5 : Lit)]
  , [(-4 : Lit), (6 : Lit), (7 : Lit)]
  , [(-2 : Lit), (7 : Lit), (8 : Lit)]
  , [(3 : Lit), (4 : Lit), (5 : Lit)]
  ]

def samp16GClosed : List Clause :=
  [ [(-3 : Lit), (1 : Lit)]
  , [(-3 : Lit), (2 : Lit)]
  , [(-2 : Lit), (1 : Lit)]
  , [(-2 : Lit), (3 : Lit)]
  , [(-1 : Lit), (2 : Lit)]
  , [(-1 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (-3 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (-1 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (1 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (2 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-8 : Lit), (1 : Lit), (7 : Lit)]
  , [(-8 : Lit), (2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (3 : Lit), (7 : Lit)]
  , [(-8 : Lit), (5 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-4 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (1 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (2 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-7 : Lit), (1 : Lit), (8 : Lit)]
  , [(-7 : Lit), (2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (3 : Lit), (8 : Lit)]
  , [(-7 : Lit), (4 : Lit), (6 : Lit)]
  , [(-6 : Lit), (4 : Lit), (7 : Lit)]
  , [(-6 : Lit), (5 : Lit), (8 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (1 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (2 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (3 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (1 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (2 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (4 : Lit)]
  , [(-5 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-5 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-5 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-5 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-5 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-5 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (6 : Lit), (8 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (1 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (2 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (5 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (5 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (6 : Lit), (7 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (1 : Lit), (4 : Lit)]
  , [(-3 : Lit), (1 : Lit), (5 : Lit)]
  , [(-3 : Lit), (1 : Lit), (7 : Lit)]
  , [(-3 : Lit), (1 : Lit), (8 : Lit)]
  , [(-3 : Lit), (2 : Lit), (4 : Lit)]
  , [(-3 : Lit), (2 : Lit), (5 : Lit)]
  , [(-3 : Lit), (2 : Lit), (7 : Lit)]
  , [(-3 : Lit), (2 : Lit), (8 : Lit)]
  , [(-3 : Lit), (7 : Lit), (8 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (1 : Lit), (4 : Lit)]
  , [(-2 : Lit), (1 : Lit), (5 : Lit)]
  , [(-2 : Lit), (1 : Lit), (7 : Lit)]
  , [(-2 : Lit), (1 : Lit), (8 : Lit)]
  , [(-2 : Lit), (3 : Lit), (4 : Lit)]
  , [(-2 : Lit), (3 : Lit), (5 : Lit)]
  , [(-2 : Lit), (3 : Lit), (7 : Lit)]
  , [(-2 : Lit), (3 : Lit), (8 : Lit)]
  , [(-2 : Lit), (7 : Lit), (8 : Lit)]
  , [(-1 : Lit), (2 : Lit), (3 : Lit)]
  , [(-1 : Lit), (2 : Lit), (4 : Lit)]
  , [(-1 : Lit), (2 : Lit), (5 : Lit)]
  , [(-1 : Lit), (2 : Lit), (7 : Lit)]
  , [(-1 : Lit), (2 : Lit), (8 : Lit)]
  , [(-1 : Lit), (3 : Lit), (4 : Lit)]
  , [(-1 : Lit), (3 : Lit), (5 : Lit)]
  , [(-1 : Lit), (3 : Lit), (7 : Lit)]
  , [(-1 : Lit), (3 : Lit), (8 : Lit)]
  , [(-1 : Lit), (7 : Lit), (8 : Lit)]
  , [(1 : Lit), (4 : Lit), (5 : Lit)]
  , [(2 : Lit), (4 : Lit), (5 : Lit)]
  , [(3 : Lit), (4 : Lit), (5 : Lit)]
  ]

def samp16GPivots : List Lit := [-10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

def samp16GVres : List Nat := [2, 4, 5, 6, 7, 8]

theorem samp16GVres_eq_samp : samp16GVres = samp16Vres := by native_decide

def samp16GClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem samp16G_closed_bool : samp16GClosedUnder samp16GClosed 3 samp16GPivots = true := by
  native_decide

theorem samp16G_lits_in_pivots :
    (samp16GClosed.all fun C => C.all fun lit => decide (lit ∈ samp16GPivots)) = true := by
  native_decide

theorem samp16G_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ samp16GClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ samp16GPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp samp16G_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem samp16G_mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : samp16GClosedUnder S w pivots = true)
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

def samp16GClosure : WidthClosure 3 where
  axioms := samp16GAxioms
  mem := fun C => C ∈ samp16GClosed
  axiom_mem := by
    intro C hC _
    have h : (samp16GAxioms.all fun A => samp16GClosed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact samp16G_mem_of_closed samp16G_closed_bool hC hD hRes hw (samp16G_pivot hC hRes)

theorem samp16G_no_empty : ¬ samp16GClosure.mem [] := by
  simp [samp16GClosure]
  native_decide

def samp16GProjOK : Bool :=
  samp16GClosed.all fun C =>
    !(supportedOn C samp16Vres) || samp16RClosed.contains C

theorem samp16GProjOK_true : samp16GProjOK = true := by native_decide

theorem samp16G_supported_in_R
    {C : Clause} (hG : C ∈ samp16GClosed) (hsup : supportedOn C samp16Vres = true) :
    C ∈ samp16RClosed := by
  have hall := (List.all_eq_true.mp samp16GProjOK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

def samp16GProjection : ProjectionInclusion 3 where
  gClosure := samp16GClosure
  rClosure := samp16RClosure
  Vres := samp16Vres
  holds := fun _ hG hsup => samp16G_supported_in_R hG hsup

def samp16GEliminationStep : EliminationStep 3 where
  before := samp16GClosure
  after := samp16RClosure
  V_after := samp16Vres
  preserves := fun _ hB hsup => samp16G_supported_in_R hB hsup

theorem samp16G_no_empty_of_projection :
    ¬ samp16GProjection.gClosure.mem [] :=
  no_empty_of_projection samp16GProjection samp16_closure_no_empty

theorem samp16_global_edge_iso_to_residualAxioms (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp16TopologyRename samp16RClosed = true ∧
      residualAxioms e = k4Axioms := by
  refine ⟨?_, residualAxioms_eq_k4 e⟩
  have h := samp16TopologySetEq_true
  simpa [topologySetEq, samp16TopologySetEq] using h

theorem samp16_fresh_g0_projects (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp16TopologyRename samp16RClosed = true ∧
      residualAxioms e = k4Axioms ∧
      ¬ samp16GProjection.gClosure.mem [] :=
  ⟨(samp16_global_edge_iso_to_residualAxioms e).1,
    (samp16_global_edge_iso_to_residualAxioms e).2,
    samp16G_no_empty_of_projection⟩

def samp16GDoc : String :=
  "fresh G₀ Closure₃ for samp16; ProjectionInclusion beyond packs/alts"

end PNPLab.Resolution
