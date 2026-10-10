/-
  Fresh G₀→R for hop-2 sample samp13: C_6 + chords [1, 3],[2, 5].

  Machine fact: Closure₃(G) has size 80 and excludes □; residual
  `samp13RClosed` (16) excludes □; every Closure₃(G) clause supported on
  residual edge vars lies in `samp13RClosed`.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures
import PNPLab.SampleResidualClosures

namespace PNPLab.Resolution

def samp13GAxioms : List Clause :=
  [ [(-8 : Lit), (7 : Lit)]
  , [(-7 : Lit), (8 : Lit)]
  , [(-2 : Lit), (1 : Lit)]
  , [(-1 : Lit), (2 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (2 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (-4 : Lit)]
  , [(-7 : Lit), (4 : Lit), (5 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-6 : Lit), (2 : Lit), (8 : Lit)]
  , [(-6 : Lit), (3 : Lit), (5 : Lit)]
  , [(-5 : Lit), (3 : Lit), (6 : Lit)]
  , [(-5 : Lit), (4 : Lit), (7 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (1 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-4 : Lit), (5 : Lit), (7 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-3 : Lit), (5 : Lit), (6 : Lit)]
  , [(-2 : Lit), (6 : Lit), (8 : Lit)]
  , [(1 : Lit), (3 : Lit), (4 : Lit)]
  ]

def samp13GClosed : List Clause :=
  [ [(-8 : Lit), (7 : Lit)]
  , [(-7 : Lit), (8 : Lit)]
  , [(-2 : Lit), (1 : Lit)]
  , [(-1 : Lit), (2 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-1 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (-4 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-4 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-8 : Lit), (1 : Lit), (6 : Lit)]
  , [(-8 : Lit), (1 : Lit), (7 : Lit)]
  , [(-8 : Lit), (2 : Lit), (6 : Lit)]
  , [(-8 : Lit), (2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (4 : Lit), (5 : Lit)]
  , [(-8 : Lit), (4 : Lit), (7 : Lit)]
  , [(-8 : Lit), (5 : Lit), (7 : Lit)]
  , [(-8 : Lit), (6 : Lit), (7 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-1 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (-4 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-7 : Lit), (1 : Lit), (6 : Lit)]
  , [(-7 : Lit), (1 : Lit), (8 : Lit)]
  , [(-7 : Lit), (2 : Lit), (6 : Lit)]
  , [(-7 : Lit), (2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (4 : Lit), (5 : Lit)]
  , [(-7 : Lit), (4 : Lit), (8 : Lit)]
  , [(-7 : Lit), (5 : Lit), (8 : Lit)]
  , [(-7 : Lit), (6 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-6 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-6 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-6 : Lit), (1 : Lit), (7 : Lit)]
  , [(-6 : Lit), (1 : Lit), (8 : Lit)]
  , [(-6 : Lit), (2 : Lit), (7 : Lit)]
  , [(-6 : Lit), (2 : Lit), (8 : Lit)]
  , [(-6 : Lit), (3 : Lit), (5 : Lit)]
  , [(-5 : Lit), (3 : Lit), (6 : Lit)]
  , [(-5 : Lit), (4 : Lit), (7 : Lit)]
  , [(-5 : Lit), (4 : Lit), (8 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (1 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (2 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-4 : Lit), (5 : Lit), (7 : Lit)]
  , [(-4 : Lit), (5 : Lit), (8 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-3 : Lit), (5 : Lit), (6 : Lit)]
  , [(-2 : Lit), (1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (1 : Lit), (4 : Lit)]
  , [(-2 : Lit), (1 : Lit), (6 : Lit)]
  , [(-2 : Lit), (1 : Lit), (7 : Lit)]
  , [(-2 : Lit), (1 : Lit), (8 : Lit)]
  , [(-2 : Lit), (6 : Lit), (7 : Lit)]
  , [(-2 : Lit), (6 : Lit), (8 : Lit)]
  , [(-1 : Lit), (2 : Lit), (3 : Lit)]
  , [(-1 : Lit), (2 : Lit), (4 : Lit)]
  , [(-1 : Lit), (2 : Lit), (6 : Lit)]
  , [(-1 : Lit), (2 : Lit), (7 : Lit)]
  , [(-1 : Lit), (2 : Lit), (8 : Lit)]
  , [(-1 : Lit), (6 : Lit), (7 : Lit)]
  , [(-1 : Lit), (6 : Lit), (8 : Lit)]
  , [(1 : Lit), (3 : Lit), (4 : Lit)]
  , [(2 : Lit), (3 : Lit), (4 : Lit)]
  ]

def samp13GPivots : List Lit := [-10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

def samp13GVres : List Nat := [2, 3, 4, 5, 6, 8]

theorem samp13GVres_eq_samp : samp13GVres = samp13Vres := by native_decide

def samp13GClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem samp13G_closed_bool : samp13GClosedUnder samp13GClosed 3 samp13GPivots = true := by
  native_decide

theorem samp13G_lits_in_pivots :
    (samp13GClosed.all fun C => C.all fun lit => decide (lit ∈ samp13GPivots)) = true := by
  native_decide

theorem samp13G_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ samp13GClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ samp13GPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp samp13G_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem samp13G_mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : samp13GClosedUnder S w pivots = true)
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

def samp13GClosure : WidthClosure 3 where
  axioms := samp13GAxioms
  mem := fun C => C ∈ samp13GClosed
  axiom_mem := by
    intro C hC _
    have h : (samp13GAxioms.all fun A => samp13GClosed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact samp13G_mem_of_closed samp13G_closed_bool hC hD hRes hw (samp13G_pivot hC hRes)

theorem samp13G_no_empty : ¬ samp13GClosure.mem [] := by
  simp [samp13GClosure]
  native_decide

def samp13GProjOK : Bool :=
  samp13GClosed.all fun C =>
    !(supportedOn C samp13Vres) || samp13RClosed.contains C

theorem samp13GProjOK_true : samp13GProjOK = true := by native_decide

theorem samp13G_supported_in_R
    {C : Clause} (hG : C ∈ samp13GClosed) (hsup : supportedOn C samp13Vres = true) :
    C ∈ samp13RClosed := by
  have hall := (List.all_eq_true.mp samp13GProjOK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

def samp13GProjection : ProjectionInclusion 3 where
  gClosure := samp13GClosure
  rClosure := samp13RClosure
  Vres := samp13Vres
  holds := fun _ hG hsup => samp13G_supported_in_R hG hsup

def samp13GEliminationStep : EliminationStep 3 where
  before := samp13GClosure
  after := samp13RClosure
  V_after := samp13Vres
  preserves := fun _ hB hsup => samp13G_supported_in_R hB hsup

theorem samp13G_no_empty_of_projection :
    ¬ samp13GProjection.gClosure.mem [] :=
  no_empty_of_projection samp13GProjection samp13_closure_no_empty

theorem samp13_global_edge_iso_to_residualAxioms (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp13TopologyRename samp13RClosed = true ∧
      residualAxioms e = k4Axioms := by
  refine ⟨?_, residualAxioms_eq_k4 e⟩
  have h := samp13TopologySetEq_true
  simpa [topologySetEq, samp13TopologySetEq] using h

theorem samp13_fresh_g0_projects (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp13TopologyRename samp13RClosed = true ∧
      residualAxioms e = k4Axioms ∧
      ¬ samp13GProjection.gClosure.mem [] :=
  ⟨(samp13_global_edge_iso_to_residualAxioms e).1,
    (samp13_global_edge_iso_to_residualAxioms e).2,
    samp13G_no_empty_of_projection⟩

def samp13GDoc : String :=
  "fresh G₀ Closure₃ for samp13; ProjectionInclusion beyond packs/alts"

end PNPLab.Resolution
