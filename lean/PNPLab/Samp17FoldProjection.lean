/-
  Fresh G₀→R for hop-3 sample samp17: C_7 + chords [0, 2],[1, 4].

  Machine fact: Closure₃(G) has size 146 and excludes □; residual
  `samp17RClosed` (16) excludes □; every Closure₃(G) clause supported on
  residual edge vars lies in `samp17RClosed`.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures
import PNPLab.SampleResidualClosures

namespace PNPLab.Resolution

def samp17GAxioms : List Clause :=
  [ [(-9 : Lit), (3 : Lit)]
  , [(-9 : Lit), (8 : Lit)]
  , [(-8 : Lit), (9 : Lit)]
  , [(-7 : Lit), (6 : Lit)]
  , [(-6 : Lit), (7 : Lit)]
  , [(-3 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (-5 : Lit)]
  , [(-8 : Lit), (5 : Lit), (7 : Lit)]
  , [(-7 : Lit), (5 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-6 : Lit), (2 : Lit), (4 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (7 : Lit), (8 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (2 : Lit), (6 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (4 : Lit), (6 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def samp17GClosed : List Clause :=
  [ [(-9 : Lit), (3 : Lit)]
  , [(-9 : Lit), (8 : Lit)]
  , [(-8 : Lit), (3 : Lit)]
  , [(-8 : Lit), (9 : Lit)]
  , [(-7 : Lit), (6 : Lit)]
  , [(-6 : Lit), (7 : Lit)]
  , [(-3 : Lit), (8 : Lit)]
  , [(-3 : Lit), (9 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (-5 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (6 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-9 : Lit), (1 : Lit), (3 : Lit)]
  , [(-9 : Lit), (1 : Lit), (8 : Lit)]
  , [(-9 : Lit), (2 : Lit), (3 : Lit)]
  , [(-9 : Lit), (2 : Lit), (8 : Lit)]
  , [(-9 : Lit), (3 : Lit), (5 : Lit)]
  , [(-9 : Lit), (3 : Lit), (6 : Lit)]
  , [(-9 : Lit), (3 : Lit), (7 : Lit)]
  , [(-9 : Lit), (3 : Lit), (8 : Lit)]
  , [(-9 : Lit), (5 : Lit), (6 : Lit)]
  , [(-9 : Lit), (5 : Lit), (7 : Lit)]
  , [(-9 : Lit), (5 : Lit), (8 : Lit)]
  , [(-9 : Lit), (6 : Lit), (8 : Lit)]
  , [(-9 : Lit), (7 : Lit), (8 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (-5 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (6 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-8 : Lit), (1 : Lit), (3 : Lit)]
  , [(-8 : Lit), (1 : Lit), (9 : Lit)]
  , [(-8 : Lit), (2 : Lit), (3 : Lit)]
  , [(-8 : Lit), (2 : Lit), (9 : Lit)]
  , [(-8 : Lit), (3 : Lit), (5 : Lit)]
  , [(-8 : Lit), (3 : Lit), (6 : Lit)]
  , [(-8 : Lit), (3 : Lit), (7 : Lit)]
  , [(-8 : Lit), (3 : Lit), (9 : Lit)]
  , [(-8 : Lit), (5 : Lit), (6 : Lit)]
  , [(-8 : Lit), (5 : Lit), (7 : Lit)]
  , [(-8 : Lit), (5 : Lit), (9 : Lit)]
  , [(-8 : Lit), (6 : Lit), (9 : Lit)]
  , [(-8 : Lit), (7 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (6 : Lit)]
  , [(-7 : Lit), (2 : Lit), (4 : Lit)]
  , [(-7 : Lit), (2 : Lit), (6 : Lit)]
  , [(-7 : Lit), (3 : Lit), (5 : Lit)]
  , [(-7 : Lit), (3 : Lit), (6 : Lit)]
  , [(-7 : Lit), (4 : Lit), (6 : Lit)]
  , [(-7 : Lit), (5 : Lit), (6 : Lit)]
  , [(-7 : Lit), (5 : Lit), (8 : Lit)]
  , [(-7 : Lit), (5 : Lit), (9 : Lit)]
  , [(-7 : Lit), (6 : Lit), (8 : Lit)]
  , [(-7 : Lit), (6 : Lit), (9 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-6 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-6 : Lit), (2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (2 : Lit), (7 : Lit)]
  , [(-6 : Lit), (3 : Lit), (5 : Lit)]
  , [(-6 : Lit), (3 : Lit), (7 : Lit)]
  , [(-6 : Lit), (4 : Lit), (7 : Lit)]
  , [(-6 : Lit), (5 : Lit), (7 : Lit)]
  , [(-6 : Lit), (5 : Lit), (8 : Lit)]
  , [(-6 : Lit), (5 : Lit), (9 : Lit)]
  , [(-6 : Lit), (7 : Lit), (8 : Lit)]
  , [(-6 : Lit), (7 : Lit), (9 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (3 : Lit), (6 : Lit)]
  , [(-5 : Lit), (3 : Lit), (7 : Lit)]
  , [(-5 : Lit), (6 : Lit), (8 : Lit)]
  , [(-5 : Lit), (6 : Lit), (9 : Lit)]
  , [(-5 : Lit), (7 : Lit), (8 : Lit)]
  , [(-5 : Lit), (7 : Lit), (9 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (2 : Lit), (6 : Lit)]
  , [(-4 : Lit), (2 : Lit), (7 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-3 : Lit), (1 : Lit), (8 : Lit)]
  , [(-3 : Lit), (1 : Lit), (9 : Lit)]
  , [(-3 : Lit), (2 : Lit), (8 : Lit)]
  , [(-3 : Lit), (2 : Lit), (9 : Lit)]
  , [(-3 : Lit), (5 : Lit), (6 : Lit)]
  , [(-3 : Lit), (5 : Lit), (7 : Lit)]
  , [(-3 : Lit), (5 : Lit), (8 : Lit)]
  , [(-3 : Lit), (5 : Lit), (9 : Lit)]
  , [(-3 : Lit), (6 : Lit), (8 : Lit)]
  , [(-3 : Lit), (6 : Lit), (9 : Lit)]
  , [(-3 : Lit), (7 : Lit), (8 : Lit)]
  , [(-3 : Lit), (7 : Lit), (9 : Lit)]
  , [(-3 : Lit), (8 : Lit), (9 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-2 : Lit), (4 : Lit), (6 : Lit)]
  , [(-2 : Lit), (4 : Lit), (7 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(1 : Lit), (2 : Lit), (8 : Lit)]
  , [(1 : Lit), (2 : Lit), (9 : Lit)]
  ]

def samp17GPivots : List Lit := [-11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

def samp17GVres : List Nat := [1, 2, 4, 5, 7, 9]

theorem samp17GVres_eq_samp : samp17GVres = samp17Vres := by native_decide

def samp17GClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem samp17G_closed_bool : samp17GClosedUnder samp17GClosed 3 samp17GPivots = true := by
  native_decide

theorem samp17G_lits_in_pivots :
    (samp17GClosed.all fun C => C.all fun lit => decide (lit ∈ samp17GPivots)) = true := by
  native_decide

theorem samp17G_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ samp17GClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ samp17GPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp samp17G_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem samp17G_mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : samp17GClosedUnder S w pivots = true)
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

def samp17GClosure : WidthClosure 3 where
  axioms := samp17GAxioms
  mem := fun C => C ∈ samp17GClosed
  axiom_mem := by
    intro C hC _
    have h : (samp17GAxioms.all fun A => samp17GClosed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact samp17G_mem_of_closed samp17G_closed_bool hC hD hRes hw (samp17G_pivot hC hRes)

theorem samp17G_no_empty : ¬ samp17GClosure.mem [] := by
  simp [samp17GClosure]
  native_decide

def samp17GProjOK : Bool :=
  samp17GClosed.all fun C =>
    !(supportedOn C samp17Vres) || samp17RClosed.contains C

theorem samp17GProjOK_true : samp17GProjOK = true := by native_decide

theorem samp17G_supported_in_R
    {C : Clause} (hG : C ∈ samp17GClosed) (hsup : supportedOn C samp17Vres = true) :
    C ∈ samp17RClosed := by
  have hall := (List.all_eq_true.mp samp17GProjOK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

def samp17GProjection : ProjectionInclusion 3 where
  gClosure := samp17GClosure
  rClosure := samp17RClosure
  Vres := samp17Vres
  holds := fun _ hG hsup => samp17G_supported_in_R hG hsup

def samp17GEliminationStep : EliminationStep 3 where
  before := samp17GClosure
  after := samp17RClosure
  V_after := samp17Vres
  preserves := fun _ hB hsup => samp17G_supported_in_R hB hsup

theorem samp17G_no_empty_of_projection :
    ¬ samp17GProjection.gClosure.mem [] :=
  no_empty_of_projection samp17GProjection samp17_closure_no_empty

theorem samp17_global_edge_iso_to_residualAxioms (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp17TopologyRename samp17RClosed = true ∧
      residualAxioms e = k4Axioms := by
  refine ⟨?_, residualAxioms_eq_k4 e⟩
  have h := samp17TopologySetEq_true
  simpa [topologySetEq, samp17TopologySetEq] using h

theorem samp17_fresh_g0_projects (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp17TopologyRename samp17RClosed = true ∧
      residualAxioms e = k4Axioms ∧
      ¬ samp17GProjection.gClosure.mem [] :=
  ⟨(samp17_global_edge_iso_to_residualAxioms e).1,
    (samp17_global_edge_iso_to_residualAxioms e).2,
    samp17G_no_empty_of_projection⟩

def samp17GDoc : String :=
  "fresh G₀ Closure₃ for samp17; ProjectionInclusion beyond packs/alts"

end PNPLab.Resolution
