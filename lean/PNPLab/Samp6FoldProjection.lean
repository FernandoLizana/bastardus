/-
  Fresh G₀→R for hop-2 sample samp6: C_6 + chords [0, 3],[1, 4].

  Machine fact: Closure₃(G) has size 68 and excludes □; residual
  `samp6RClosed` (16) excludes □; every Closure₃(G) clause supported on
  residual edge vars lies in `samp6RClosed`.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures
import PNPLab.SampleResidualClosures

namespace PNPLab.Resolution

def samp6GAxioms : List Clause :=
  [ [(-8 : Lit), (3 : Lit)]
  , [(-6 : Lit), (4 : Lit)]
  , [(-4 : Lit), (6 : Lit)]
  , [(-3 : Lit), (8 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (-5 : Lit)]
  , [(-8 : Lit), (5 : Lit), (7 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-7 : Lit), (2 : Lit), (6 : Lit)]
  , [(-7 : Lit), (5 : Lit), (8 : Lit)]
  , [(-6 : Lit), (2 : Lit), (7 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (7 : Lit), (8 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (6 : Lit), (7 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def samp6GClosed : List Clause :=
  [ [(-8 : Lit), (3 : Lit)]
  , [(-6 : Lit), (4 : Lit)]
  , [(-4 : Lit), (6 : Lit)]
  , [(-3 : Lit), (8 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (-5 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-8 : Lit), (1 : Lit), (3 : Lit)]
  , [(-8 : Lit), (2 : Lit), (3 : Lit)]
  , [(-8 : Lit), (3 : Lit), (5 : Lit)]
  , [(-8 : Lit), (3 : Lit), (7 : Lit)]
  , [(-8 : Lit), (5 : Lit), (7 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (4 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-7 : Lit), (2 : Lit), (4 : Lit)]
  , [(-7 : Lit), (2 : Lit), (6 : Lit)]
  , [(-7 : Lit), (3 : Lit), (5 : Lit)]
  , [(-7 : Lit), (5 : Lit), (8 : Lit)]
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
  , [(-5 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (3 : Lit), (7 : Lit)]
  , [(-5 : Lit), (7 : Lit), (8 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (6 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (6 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (1 : Lit), (6 : Lit)]
  , [(-4 : Lit), (2 : Lit), (6 : Lit)]
  , [(-4 : Lit), (2 : Lit), (7 : Lit)]
  , [(-4 : Lit), (5 : Lit), (6 : Lit)]
  , [(-4 : Lit), (6 : Lit), (7 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-3 : Lit), (1 : Lit), (8 : Lit)]
  , [(-3 : Lit), (2 : Lit), (8 : Lit)]
  , [(-3 : Lit), (5 : Lit), (7 : Lit)]
  , [(-3 : Lit), (5 : Lit), (8 : Lit)]
  , [(-3 : Lit), (7 : Lit), (8 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-2 : Lit), (4 : Lit), (7 : Lit)]
  , [(-2 : Lit), (6 : Lit), (7 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(1 : Lit), (2 : Lit), (8 : Lit)]
  ]

def samp6GPivots : List Lit := [-10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

def samp6GVres : List Nat := [1, 2, 5, 6, 7, 8]

theorem samp6GVres_eq_samp : samp6GVres = samp6Vres := by native_decide

def samp6GClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem samp6G_closed_bool : samp6GClosedUnder samp6GClosed 3 samp6GPivots = true := by
  native_decide

theorem samp6G_lits_in_pivots :
    (samp6GClosed.all fun C => C.all fun lit => decide (lit ∈ samp6GPivots)) = true := by
  native_decide

theorem samp6G_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ samp6GClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ samp6GPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp samp6G_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem samp6G_mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : samp6GClosedUnder S w pivots = true)
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

def samp6GClosure : WidthClosure 3 where
  axioms := samp6GAxioms
  mem := fun C => C ∈ samp6GClosed
  axiom_mem := by
    intro C hC _
    have h : (samp6GAxioms.all fun A => samp6GClosed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact samp6G_mem_of_closed samp6G_closed_bool hC hD hRes hw (samp6G_pivot hC hRes)

theorem samp6G_no_empty : ¬ samp6GClosure.mem [] := by
  simp [samp6GClosure]
  native_decide

def samp6GProjOK : Bool :=
  samp6GClosed.all fun C =>
    !(supportedOn C samp6Vres) || samp6RClosed.contains C

theorem samp6GProjOK_true : samp6GProjOK = true := by native_decide

theorem samp6G_supported_in_R
    {C : Clause} (hG : C ∈ samp6GClosed) (hsup : supportedOn C samp6Vres = true) :
    C ∈ samp6RClosed := by
  have hall := (List.all_eq_true.mp samp6GProjOK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

def samp6GProjection : ProjectionInclusion 3 where
  gClosure := samp6GClosure
  rClosure := samp6RClosure
  Vres := samp6Vres
  holds := fun _ hG hsup => samp6G_supported_in_R hG hsup

def samp6GEliminationStep : EliminationStep 3 where
  before := samp6GClosure
  after := samp6RClosure
  V_after := samp6Vres
  preserves := fun _ hB hsup => samp6G_supported_in_R hB hsup

theorem samp6G_no_empty_of_projection :
    ¬ samp6GProjection.gClosure.mem [] :=
  no_empty_of_projection samp6GProjection samp6_closure_no_empty

theorem samp6_global_edge_iso_to_residualAxioms (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp6TopologyRename samp6RClosed = true ∧
      residualAxioms e = k4Axioms := by
  refine ⟨?_, residualAxioms_eq_k4 e⟩
  have h := samp6TopologySetEq_true
  simpa [topologySetEq, samp6TopologySetEq] using h

theorem samp6_fresh_g0_projects (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp6TopologyRename samp6RClosed = true ∧
      residualAxioms e = k4Axioms ∧
      ¬ samp6GProjection.gClosure.mem [] :=
  ⟨(samp6_global_edge_iso_to_residualAxioms e).1,
    (samp6_global_edge_iso_to_residualAxioms e).2,
    samp6G_no_empty_of_projection⟩

def samp6GDoc : String :=
  "fresh G₀ Closure₃ for samp6; ProjectionInclusion beyond packs/alts"

end PNPLab.Resolution
