/-
  Fresh G₀→R for hop-2 sample samp14: C_6 + chords [1, 4],[2, 5].

  Machine fact: Closure₃(G) has size 68 and excludes □; residual
  `samp14RClosed` (16) excludes □; every Closure₃(G) clause supported on
  residual edge vars lies in `samp14RClosed`.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures
import PNPLab.SampleResidualClosures

namespace PNPLab.Resolution

def samp14GAxioms : List Clause :=
  [ [(-7 : Lit), (5 : Lit)]
  , [(-5 : Lit), (7 : Lit)]
  , [(-2 : Lit), (1 : Lit)]
  , [(-1 : Lit), (2 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (-4 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (2 : Lit), (6 : Lit)]
  , [(-8 : Lit), (4 : Lit), (7 : Lit)]
  , [(-7 : Lit), (4 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-6 : Lit), (2 : Lit), (8 : Lit)]
  , [(-6 : Lit), (3 : Lit), (5 : Lit)]
  , [(-5 : Lit), (3 : Lit), (6 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (1 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-4 : Lit), (7 : Lit), (8 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-3 : Lit), (5 : Lit), (6 : Lit)]
  , [(-2 : Lit), (6 : Lit), (8 : Lit)]
  , [(1 : Lit), (3 : Lit), (4 : Lit)]
  ]

def samp14GClosed : List Clause :=
  [ [(-7 : Lit), (5 : Lit)]
  , [(-5 : Lit), (7 : Lit)]
  , [(-2 : Lit), (1 : Lit)]
  , [(-1 : Lit), (2 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (-4 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (5 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-1 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (-4 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-8 : Lit), (1 : Lit), (6 : Lit)]
  , [(-8 : Lit), (2 : Lit), (6 : Lit)]
  , [(-8 : Lit), (4 : Lit), (5 : Lit)]
  , [(-8 : Lit), (4 : Lit), (7 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-3 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (5 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (5 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (5 : Lit)]
  , [(-7 : Lit), (3 : Lit), (5 : Lit)]
  , [(-7 : Lit), (3 : Lit), (6 : Lit)]
  , [(-7 : Lit), (4 : Lit), (5 : Lit)]
  , [(-7 : Lit), (4 : Lit), (8 : Lit)]
  , [(-7 : Lit), (5 : Lit), (6 : Lit)]
  , [(-7 : Lit), (5 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-6 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-6 : Lit), (1 : Lit), (8 : Lit)]
  , [(-6 : Lit), (2 : Lit), (8 : Lit)]
  , [(-6 : Lit), (3 : Lit), (5 : Lit)]
  , [(-6 : Lit), (3 : Lit), (7 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (7 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (7 : Lit)]
  , [(-5 : Lit), (3 : Lit), (6 : Lit)]
  , [(-5 : Lit), (3 : Lit), (7 : Lit)]
  , [(-5 : Lit), (4 : Lit), (7 : Lit)]
  , [(-5 : Lit), (4 : Lit), (8 : Lit)]
  , [(-5 : Lit), (6 : Lit), (7 : Lit)]
  , [(-5 : Lit), (7 : Lit), (8 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (1 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (2 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-4 : Lit), (5 : Lit), (8 : Lit)]
  , [(-4 : Lit), (7 : Lit), (8 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-3 : Lit), (5 : Lit), (6 : Lit)]
  , [(-3 : Lit), (6 : Lit), (7 : Lit)]
  , [(-2 : Lit), (1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (1 : Lit), (4 : Lit)]
  , [(-2 : Lit), (1 : Lit), (6 : Lit)]
  , [(-2 : Lit), (1 : Lit), (8 : Lit)]
  , [(-2 : Lit), (6 : Lit), (8 : Lit)]
  , [(-1 : Lit), (2 : Lit), (3 : Lit)]
  , [(-1 : Lit), (2 : Lit), (4 : Lit)]
  , [(-1 : Lit), (2 : Lit), (6 : Lit)]
  , [(-1 : Lit), (2 : Lit), (8 : Lit)]
  , [(-1 : Lit), (6 : Lit), (8 : Lit)]
  , [(1 : Lit), (3 : Lit), (4 : Lit)]
  , [(2 : Lit), (3 : Lit), (4 : Lit)]
  ]

def samp14GPivots : List Lit := [-10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

def samp14GVres : List Nat := [2, 3, 4, 6, 7, 8]

theorem samp14GVres_eq_samp : samp14GVres = samp14Vres := by native_decide

def samp14GClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem samp14G_closed_bool : samp14GClosedUnder samp14GClosed 3 samp14GPivots = true := by
  native_decide

theorem samp14G_lits_in_pivots :
    (samp14GClosed.all fun C => C.all fun lit => decide (lit ∈ samp14GPivots)) = true := by
  native_decide

theorem samp14G_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ samp14GClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ samp14GPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp samp14G_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem samp14G_mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : samp14GClosedUnder S w pivots = true)
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

def samp14GClosure : WidthClosure 3 where
  axioms := samp14GAxioms
  mem := fun C => C ∈ samp14GClosed
  axiom_mem := by
    intro C hC _
    have h : (samp14GAxioms.all fun A => samp14GClosed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact samp14G_mem_of_closed samp14G_closed_bool hC hD hRes hw (samp14G_pivot hC hRes)

theorem samp14G_no_empty : ¬ samp14GClosure.mem [] := by
  simp [samp14GClosure]
  native_decide

def samp14GProjOK : Bool :=
  samp14GClosed.all fun C =>
    !(supportedOn C samp14Vres) || samp14RClosed.contains C

theorem samp14GProjOK_true : samp14GProjOK = true := by native_decide

theorem samp14G_supported_in_R
    {C : Clause} (hG : C ∈ samp14GClosed) (hsup : supportedOn C samp14Vres = true) :
    C ∈ samp14RClosed := by
  have hall := (List.all_eq_true.mp samp14GProjOK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

def samp14GProjection : ProjectionInclusion 3 where
  gClosure := samp14GClosure
  rClosure := samp14RClosure
  Vres := samp14Vres
  holds := fun _ hG hsup => samp14G_supported_in_R hG hsup

def samp14GEliminationStep : EliminationStep 3 where
  before := samp14GClosure
  after := samp14RClosure
  V_after := samp14Vres
  preserves := fun _ hB hsup => samp14G_supported_in_R hB hsup

theorem samp14G_no_empty_of_projection :
    ¬ samp14GProjection.gClosure.mem [] :=
  no_empty_of_projection samp14GProjection samp14_closure_no_empty

theorem samp14_global_edge_iso_to_residualAxioms (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp14TopologyRename samp14RClosed = true ∧
      residualAxioms e = k4Axioms := by
  refine ⟨?_, residualAxioms_eq_k4 e⟩
  have h := samp14TopologySetEq_true
  simpa [topologySetEq, samp14TopologySetEq] using h

theorem samp14_fresh_g0_projects (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp14TopologyRename samp14RClosed = true ∧
      residualAxioms e = k4Axioms ∧
      ¬ samp14GProjection.gClosure.mem [] :=
  ⟨(samp14_global_edge_iso_to_residualAxioms e).1,
    (samp14_global_edge_iso_to_residualAxioms e).2,
    samp14G_no_empty_of_projection⟩

def samp14GDoc : String :=
  "fresh G₀ Closure₃ for samp14; ProjectionInclusion beyond packs/alts"

end PNPLab.Resolution
