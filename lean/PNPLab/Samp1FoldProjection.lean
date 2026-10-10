/-
  Fresh G₀→R for hop-1 sample samp1: C_5 + chords [0, 3],[1, 4].

  Machine fact: Closure₃(G) has size 42 and excludes □; residual
  `samp1RClosed` (16) excludes □; every Closure₃(G) clause supported on
  residual edge vars lies in `samp1RClosed`.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures
import PNPLab.SampleResidualClosures

namespace PNPLab.Resolution

def samp1GAxioms : List Clause :=
  [ [(-6 : Lit), (4 : Lit)]
  , [(-4 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-7 : Lit), (2 : Lit), (6 : Lit)]
  , [(-7 : Lit), (3 : Lit), (5 : Lit)]
  , [(-6 : Lit), (2 : Lit), (7 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (3 : Lit), (7 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (5 : Lit), (7 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (6 : Lit), (7 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def samp1GClosed : List Clause :=
  [ [(-6 : Lit), (4 : Lit)]
  , [(-4 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (4 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (6 : Lit)]
  , [(-7 : Lit), (2 : Lit), (4 : Lit)]
  , [(-7 : Lit), (2 : Lit), (6 : Lit)]
  , [(-7 : Lit), (3 : Lit), (5 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (4 : Lit)]
  , [(-6 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-6 : Lit), (1 : Lit), (4 : Lit)]
  , [(-6 : Lit), (1 : Lit), (5 : Lit)]
  , [(-6 : Lit), (2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (2 : Lit), (7 : Lit)]
  , [(-6 : Lit), (4 : Lit), (5 : Lit)]
  , [(-6 : Lit), (4 : Lit), (7 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (6 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (3 : Lit), (7 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (6 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (6 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (1 : Lit), (6 : Lit)]
  , [(-4 : Lit), (2 : Lit), (6 : Lit)]
  , [(-4 : Lit), (2 : Lit), (7 : Lit)]
  , [(-4 : Lit), (5 : Lit), (6 : Lit)]
  , [(-4 : Lit), (6 : Lit), (7 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (5 : Lit), (7 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (4 : Lit), (7 : Lit)]
  , [(-2 : Lit), (6 : Lit), (7 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def samp1GPivots : List Lit := [-10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

def samp1GVres : List Nat := [1, 2, 3, 5, 6, 7]

theorem samp1GVres_eq_samp : samp1GVres = samp1Vres := by native_decide

def samp1GClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem samp1G_closed_bool : samp1GClosedUnder samp1GClosed 3 samp1GPivots = true := by
  native_decide

theorem samp1G_lits_in_pivots :
    (samp1GClosed.all fun C => C.all fun lit => decide (lit ∈ samp1GPivots)) = true := by
  native_decide

theorem samp1G_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ samp1GClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ samp1GPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp samp1G_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem samp1G_mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : samp1GClosedUnder S w pivots = true)
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

def samp1GClosure : WidthClosure 3 where
  axioms := samp1GAxioms
  mem := fun C => C ∈ samp1GClosed
  axiom_mem := by
    intro C hC _
    have h : (samp1GAxioms.all fun A => samp1GClosed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact samp1G_mem_of_closed samp1G_closed_bool hC hD hRes hw (samp1G_pivot hC hRes)

theorem samp1G_no_empty : ¬ samp1GClosure.mem [] := by
  simp [samp1GClosure]
  native_decide

def samp1GProjOK : Bool :=
  samp1GClosed.all fun C =>
    !(supportedOn C samp1Vres) || samp1RClosed.contains C

theorem samp1GProjOK_true : samp1GProjOK = true := by native_decide

theorem samp1G_supported_in_R
    {C : Clause} (hG : C ∈ samp1GClosed) (hsup : supportedOn C samp1Vres = true) :
    C ∈ samp1RClosed := by
  have hall := (List.all_eq_true.mp samp1GProjOK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

def samp1GProjection : ProjectionInclusion 3 where
  gClosure := samp1GClosure
  rClosure := samp1RClosure
  Vres := samp1Vres
  holds := fun _ hG hsup => samp1G_supported_in_R hG hsup

def samp1GEliminationStep : EliminationStep 3 where
  before := samp1GClosure
  after := samp1RClosure
  V_after := samp1Vres
  preserves := fun _ hB hsup => samp1G_supported_in_R hB hsup

theorem samp1G_no_empty_of_projection :
    ¬ samp1GProjection.gClosure.mem [] :=
  no_empty_of_projection samp1GProjection samp1_closure_no_empty

/-- Reuses `samp1_global_edge_iso_to_residualAxioms` from SampleResidualClosures. -/
theorem samp1_fresh_g0_projects (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp1TopologyRename samp1RClosed = true ∧
      residualAxioms e = k4Axioms ∧
      ¬ samp1GProjection.gClosure.mem [] :=
  ⟨(samp1_global_edge_iso_to_residualAxioms e).1,
    (samp1_global_edge_iso_to_residualAxioms e).2,
    samp1G_no_empty_of_projection⟩

def samp1GDoc : String :=
  "fresh G₀ Closure₃ for samp1; ProjectionInclusion beyond packs/alts"

end PNPLab.Resolution
