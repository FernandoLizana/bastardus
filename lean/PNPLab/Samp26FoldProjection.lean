/-
  Fresh G₀→R for hop-3 sample samp26: C_7 + chords [0, 4],[1, 6].

  Machine fact: Closure₃(G) has size 146 and excludes □; residual
  `samp26RClosed` (16) excludes □; every Closure₃(G) clause supported on
  residual edge vars lies in `samp26RClosed`.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures
import PNPLab.SampleResidualClosures

namespace PNPLab.Resolution

def samp26GAxioms : List Clause :=
  [ [(-9 : Lit), (8 : Lit)]
  , [(-8 : Lit), (9 : Lit)]
  , [(-7 : Lit), (6 : Lit)]
  , [(-6 : Lit), (4 : Lit)]
  , [(-6 : Lit), (7 : Lit)]
  , [(-4 : Lit), (6 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-9 : Lit), (3 : Lit), (5 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (2 : Lit), (7 : Lit)]
  , [(-7 : Lit), (2 : Lit), (8 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (3 : Lit), (9 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (5 : Lit), (9 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (7 : Lit), (8 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def samp26GClosed : List Clause :=
  [ [(-9 : Lit), (8 : Lit)]
  , [(-8 : Lit), (9 : Lit)]
  , [(-7 : Lit), (4 : Lit)]
  , [(-7 : Lit), (6 : Lit)]
  , [(-6 : Lit), (4 : Lit)]
  , [(-6 : Lit), (7 : Lit)]
  , [(-4 : Lit), (6 : Lit)]
  , [(-4 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (-2 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (4 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (6 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (4 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-9 : Lit), (-4 : Lit), (6 : Lit)]
  , [(-9 : Lit), (-4 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-4 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-9 : Lit), (2 : Lit), (4 : Lit)]
  , [(-9 : Lit), (2 : Lit), (6 : Lit)]
  , [(-9 : Lit), (2 : Lit), (7 : Lit)]
  , [(-9 : Lit), (2 : Lit), (8 : Lit)]
  , [(-9 : Lit), (3 : Lit), (5 : Lit)]
  , [(-9 : Lit), (3 : Lit), (8 : Lit)]
  , [(-9 : Lit), (4 : Lit), (8 : Lit)]
  , [(-9 : Lit), (5 : Lit), (8 : Lit)]
  , [(-9 : Lit), (6 : Lit), (8 : Lit)]
  , [(-9 : Lit), (7 : Lit), (8 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (4 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (6 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (4 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (-4 : Lit), (6 : Lit)]
  , [(-8 : Lit), (-4 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-4 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-8 : Lit), (2 : Lit), (4 : Lit)]
  , [(-8 : Lit), (2 : Lit), (6 : Lit)]
  , [(-8 : Lit), (2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (2 : Lit), (9 : Lit)]
  , [(-8 : Lit), (3 : Lit), (5 : Lit)]
  , [(-8 : Lit), (3 : Lit), (9 : Lit)]
  , [(-8 : Lit), (4 : Lit), (9 : Lit)]
  , [(-8 : Lit), (5 : Lit), (9 : Lit)]
  , [(-8 : Lit), (6 : Lit), (9 : Lit)]
  , [(-8 : Lit), (7 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (4 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (4 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (6 : Lit)]
  , [(-7 : Lit), (1 : Lit), (4 : Lit)]
  , [(-7 : Lit), (1 : Lit), (5 : Lit)]
  , [(-7 : Lit), (1 : Lit), (6 : Lit)]
  , [(-7 : Lit), (2 : Lit), (4 : Lit)]
  , [(-7 : Lit), (2 : Lit), (6 : Lit)]
  , [(-7 : Lit), (2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (2 : Lit), (9 : Lit)]
  , [(-7 : Lit), (4 : Lit), (5 : Lit)]
  , [(-7 : Lit), (4 : Lit), (6 : Lit)]
  , [(-7 : Lit), (4 : Lit), (8 : Lit)]
  , [(-7 : Lit), (4 : Lit), (9 : Lit)]
  , [(-7 : Lit), (5 : Lit), (6 : Lit)]
  , [(-7 : Lit), (6 : Lit), (8 : Lit)]
  , [(-7 : Lit), (6 : Lit), (9 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (4 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-6 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-6 : Lit), (1 : Lit), (4 : Lit)]
  , [(-6 : Lit), (1 : Lit), (5 : Lit)]
  , [(-6 : Lit), (1 : Lit), (7 : Lit)]
  , [(-6 : Lit), (2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (2 : Lit), (7 : Lit)]
  , [(-6 : Lit), (2 : Lit), (8 : Lit)]
  , [(-6 : Lit), (2 : Lit), (9 : Lit)]
  , [(-6 : Lit), (4 : Lit), (5 : Lit)]
  , [(-6 : Lit), (4 : Lit), (7 : Lit)]
  , [(-6 : Lit), (4 : Lit), (8 : Lit)]
  , [(-6 : Lit), (4 : Lit), (9 : Lit)]
  , [(-6 : Lit), (5 : Lit), (7 : Lit)]
  , [(-6 : Lit), (7 : Lit), (8 : Lit)]
  , [(-6 : Lit), (7 : Lit), (9 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (6 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (7 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (1 : Lit), (7 : Lit)]
  , [(-5 : Lit), (3 : Lit), (8 : Lit)]
  , [(-5 : Lit), (3 : Lit), (9 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (6 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (6 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (1 : Lit), (6 : Lit)]
  , [(-4 : Lit), (1 : Lit), (7 : Lit)]
  , [(-4 : Lit), (2 : Lit), (6 : Lit)]
  , [(-4 : Lit), (2 : Lit), (7 : Lit)]
  , [(-4 : Lit), (2 : Lit), (8 : Lit)]
  , [(-4 : Lit), (2 : Lit), (9 : Lit)]
  , [(-4 : Lit), (5 : Lit), (6 : Lit)]
  , [(-4 : Lit), (5 : Lit), (7 : Lit)]
  , [(-4 : Lit), (6 : Lit), (7 : Lit)]
  , [(-4 : Lit), (6 : Lit), (8 : Lit)]
  , [(-4 : Lit), (6 : Lit), (9 : Lit)]
  , [(-4 : Lit), (7 : Lit), (8 : Lit)]
  , [(-4 : Lit), (7 : Lit), (9 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (5 : Lit), (8 : Lit)]
  , [(-3 : Lit), (5 : Lit), (9 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (4 : Lit), (8 : Lit)]
  , [(-2 : Lit), (4 : Lit), (9 : Lit)]
  , [(-2 : Lit), (6 : Lit), (8 : Lit)]
  , [(-2 : Lit), (6 : Lit), (9 : Lit)]
  , [(-2 : Lit), (7 : Lit), (8 : Lit)]
  , [(-2 : Lit), (7 : Lit), (9 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(-1 : Lit), (5 : Lit), (7 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def samp26GPivots : List Lit := [-11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

def samp26GVres : List Nat := [1, 2, 3, 5, 6, 9]

theorem samp26GVres_eq_samp : samp26GVres = samp26Vres := by native_decide

def samp26GClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem samp26G_closed_bool : samp26GClosedUnder samp26GClosed 3 samp26GPivots = true := by
  native_decide

theorem samp26G_lits_in_pivots :
    (samp26GClosed.all fun C => C.all fun lit => decide (lit ∈ samp26GPivots)) = true := by
  native_decide

theorem samp26G_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ samp26GClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ samp26GPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp samp26G_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem samp26G_mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : samp26GClosedUnder S w pivots = true)
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

def samp26GClosure : WidthClosure 3 where
  axioms := samp26GAxioms
  mem := fun C => C ∈ samp26GClosed
  axiom_mem := by
    intro C hC _
    have h : (samp26GAxioms.all fun A => samp26GClosed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact samp26G_mem_of_closed samp26G_closed_bool hC hD hRes hw (samp26G_pivot hC hRes)

theorem samp26G_no_empty : ¬ samp26GClosure.mem [] := by
  simp [samp26GClosure]
  native_decide

def samp26GProjOK : Bool :=
  samp26GClosed.all fun C =>
    !(supportedOn C samp26Vres) || samp26RClosed.contains C

theorem samp26GProjOK_true : samp26GProjOK = true := by native_decide

theorem samp26G_supported_in_R
    {C : Clause} (hG : C ∈ samp26GClosed) (hsup : supportedOn C samp26Vres = true) :
    C ∈ samp26RClosed := by
  have hall := (List.all_eq_true.mp samp26GProjOK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

def samp26GProjection : ProjectionInclusion 3 where
  gClosure := samp26GClosure
  rClosure := samp26RClosure
  Vres := samp26Vres
  holds := fun _ hG hsup => samp26G_supported_in_R hG hsup

def samp26GEliminationStep : EliminationStep 3 where
  before := samp26GClosure
  after := samp26RClosure
  V_after := samp26Vres
  preserves := fun _ hB hsup => samp26G_supported_in_R hB hsup

theorem samp26G_no_empty_of_projection :
    ¬ samp26GProjection.gClosure.mem [] :=
  no_empty_of_projection samp26GProjection samp26_closure_no_empty

theorem samp26_global_edge_iso_to_residualAxioms (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp26TopologyRename samp26RClosed = true ∧
      residualAxioms e = k4Axioms := by
  refine ⟨?_, residualAxioms_eq_k4 e⟩
  have h := samp26TopologySetEq_true
  simpa [topologySetEq, samp26TopologySetEq] using h

theorem samp26_fresh_g0_projects (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp26TopologyRename samp26RClosed = true ∧
      residualAxioms e = k4Axioms ∧
      ¬ samp26GProjection.gClosure.mem [] :=
  ⟨(samp26_global_edge_iso_to_residualAxioms e).1,
    (samp26_global_edge_iso_to_residualAxioms e).2,
    samp26G_no_empty_of_projection⟩

def samp26GDoc : String :=
  "fresh G₀ Closure₃ for samp26; ProjectionInclusion beyond packs/alts"

end PNPLab.Resolution
