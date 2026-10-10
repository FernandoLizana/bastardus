/-
  Fresh G₀→R for hop-3 sample samp22: C_7 + chords [0, 3],[1, 6].

  Machine fact: Closure₃(G) has size 146 and excludes □; residual
  `samp22RClosed` (16) excludes □; every Closure₃(G) clause supported on
  residual edge vars lies in `samp22RClosed`.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures
import PNPLab.SampleResidualClosures

namespace PNPLab.Resolution

def samp22GAxioms : List Clause :=
  [ [(-9 : Lit), (8 : Lit)]
  , [(-8 : Lit), (7 : Lit)]
  , [(-8 : Lit), (9 : Lit)]
  , [(-7 : Lit), (8 : Lit)]
  , [(-6 : Lit), (4 : Lit)]
  , [(-4 : Lit), (6 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-9 : Lit), (3 : Lit), (5 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-7 : Lit), (2 : Lit), (6 : Lit)]
  , [(-6 : Lit), (2 : Lit), (7 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (3 : Lit), (9 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (5 : Lit), (9 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (6 : Lit), (7 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def samp22GClosed : List Clause :=
  [ [(-9 : Lit), (7 : Lit)]
  , [(-9 : Lit), (8 : Lit)]
  , [(-8 : Lit), (7 : Lit)]
  , [(-8 : Lit), (9 : Lit)]
  , [(-7 : Lit), (8 : Lit)]
  , [(-7 : Lit), (9 : Lit)]
  , [(-6 : Lit), (4 : Lit)]
  , [(-4 : Lit), (6 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (4 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-9 : Lit), (-4 : Lit), (6 : Lit)]
  , [(-9 : Lit), (-4 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-4 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-9 : Lit), (2 : Lit), (4 : Lit)]
  , [(-9 : Lit), (2 : Lit), (6 : Lit)]
  , [(-9 : Lit), (2 : Lit), (7 : Lit)]
  , [(-9 : Lit), (2 : Lit), (8 : Lit)]
  , [(-9 : Lit), (3 : Lit), (5 : Lit)]
  , [(-9 : Lit), (3 : Lit), (7 : Lit)]
  , [(-9 : Lit), (3 : Lit), (8 : Lit)]
  , [(-9 : Lit), (4 : Lit), (7 : Lit)]
  , [(-9 : Lit), (4 : Lit), (8 : Lit)]
  , [(-9 : Lit), (5 : Lit), (7 : Lit)]
  , [(-9 : Lit), (5 : Lit), (8 : Lit)]
  , [(-9 : Lit), (6 : Lit), (7 : Lit)]
  , [(-9 : Lit), (6 : Lit), (8 : Lit)]
  , [(-9 : Lit), (7 : Lit), (8 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (4 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (-4 : Lit), (6 : Lit)]
  , [(-8 : Lit), (-4 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-4 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-8 : Lit), (2 : Lit), (4 : Lit)]
  , [(-8 : Lit), (2 : Lit), (6 : Lit)]
  , [(-8 : Lit), (2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (2 : Lit), (9 : Lit)]
  , [(-8 : Lit), (3 : Lit), (5 : Lit)]
  , [(-8 : Lit), (3 : Lit), (7 : Lit)]
  , [(-8 : Lit), (3 : Lit), (9 : Lit)]
  , [(-8 : Lit), (4 : Lit), (7 : Lit)]
  , [(-8 : Lit), (4 : Lit), (9 : Lit)]
  , [(-8 : Lit), (5 : Lit), (7 : Lit)]
  , [(-8 : Lit), (5 : Lit), (9 : Lit)]
  , [(-8 : Lit), (6 : Lit), (7 : Lit)]
  , [(-8 : Lit), (6 : Lit), (9 : Lit)]
  , [(-8 : Lit), (7 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (4 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-7 : Lit), (2 : Lit), (4 : Lit)]
  , [(-7 : Lit), (2 : Lit), (6 : Lit)]
  , [(-7 : Lit), (2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (2 : Lit), (9 : Lit)]
  , [(-7 : Lit), (3 : Lit), (5 : Lit)]
  , [(-7 : Lit), (3 : Lit), (8 : Lit)]
  , [(-7 : Lit), (3 : Lit), (9 : Lit)]
  , [(-7 : Lit), (4 : Lit), (8 : Lit)]
  , [(-7 : Lit), (4 : Lit), (9 : Lit)]
  , [(-7 : Lit), (5 : Lit), (8 : Lit)]
  , [(-7 : Lit), (5 : Lit), (9 : Lit)]
  , [(-7 : Lit), (6 : Lit), (8 : Lit)]
  , [(-7 : Lit), (6 : Lit), (9 : Lit)]
  , [(-7 : Lit), (8 : Lit), (9 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (4 : Lit)]
  , [(-6 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-6 : Lit), (1 : Lit), (4 : Lit)]
  , [(-6 : Lit), (1 : Lit), (5 : Lit)]
  , [(-6 : Lit), (2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (2 : Lit), (7 : Lit)]
  , [(-6 : Lit), (2 : Lit), (8 : Lit)]
  , [(-6 : Lit), (2 : Lit), (9 : Lit)]
  , [(-6 : Lit), (4 : Lit), (5 : Lit)]
  , [(-6 : Lit), (4 : Lit), (7 : Lit)]
  , [(-6 : Lit), (4 : Lit), (8 : Lit)]
  , [(-6 : Lit), (4 : Lit), (9 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (6 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (3 : Lit), (7 : Lit)]
  , [(-5 : Lit), (3 : Lit), (8 : Lit)]
  , [(-5 : Lit), (3 : Lit), (9 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (6 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (6 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (1 : Lit), (6 : Lit)]
  , [(-4 : Lit), (2 : Lit), (6 : Lit)]
  , [(-4 : Lit), (2 : Lit), (7 : Lit)]
  , [(-4 : Lit), (2 : Lit), (8 : Lit)]
  , [(-4 : Lit), (2 : Lit), (9 : Lit)]
  , [(-4 : Lit), (5 : Lit), (6 : Lit)]
  , [(-4 : Lit), (6 : Lit), (7 : Lit)]
  , [(-4 : Lit), (6 : Lit), (8 : Lit)]
  , [(-4 : Lit), (6 : Lit), (9 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (5 : Lit), (7 : Lit)]
  , [(-3 : Lit), (5 : Lit), (8 : Lit)]
  , [(-3 : Lit), (5 : Lit), (9 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (4 : Lit), (7 : Lit)]
  , [(-2 : Lit), (4 : Lit), (8 : Lit)]
  , [(-2 : Lit), (4 : Lit), (9 : Lit)]
  , [(-2 : Lit), (6 : Lit), (7 : Lit)]
  , [(-2 : Lit), (6 : Lit), (8 : Lit)]
  , [(-2 : Lit), (6 : Lit), (9 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def samp22GPivots : List Lit := [-11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

def samp22GVres : List Nat := [1, 2, 3, 5, 6, 8]

theorem samp22GVres_eq_samp : samp22GVres = samp22Vres := by native_decide

def samp22GClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem samp22G_closed_bool : samp22GClosedUnder samp22GClosed 3 samp22GPivots = true := by
  native_decide

theorem samp22G_lits_in_pivots :
    (samp22GClosed.all fun C => C.all fun lit => decide (lit ∈ samp22GPivots)) = true := by
  native_decide

theorem samp22G_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ samp22GClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ samp22GPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp samp22G_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem samp22G_mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : samp22GClosedUnder S w pivots = true)
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

def samp22GClosure : WidthClosure 3 where
  axioms := samp22GAxioms
  mem := fun C => C ∈ samp22GClosed
  axiom_mem := by
    intro C hC _
    have h : (samp22GAxioms.all fun A => samp22GClosed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact samp22G_mem_of_closed samp22G_closed_bool hC hD hRes hw (samp22G_pivot hC hRes)

theorem samp22G_no_empty : ¬ samp22GClosure.mem [] := by
  simp [samp22GClosure]
  native_decide

def samp22GProjOK : Bool :=
  samp22GClosed.all fun C =>
    !(supportedOn C samp22Vres) || samp22RClosed.contains C

theorem samp22GProjOK_true : samp22GProjOK = true := by native_decide

theorem samp22G_supported_in_R
    {C : Clause} (hG : C ∈ samp22GClosed) (hsup : supportedOn C samp22Vres = true) :
    C ∈ samp22RClosed := by
  have hall := (List.all_eq_true.mp samp22GProjOK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

def samp22GProjection : ProjectionInclusion 3 where
  gClosure := samp22GClosure
  rClosure := samp22RClosure
  Vres := samp22Vres
  holds := fun _ hG hsup => samp22G_supported_in_R hG hsup

def samp22GEliminationStep : EliminationStep 3 where
  before := samp22GClosure
  after := samp22RClosure
  V_after := samp22Vres
  preserves := fun _ hB hsup => samp22G_supported_in_R hB hsup

theorem samp22G_no_empty_of_projection :
    ¬ samp22GProjection.gClosure.mem [] :=
  no_empty_of_projection samp22GProjection samp22_closure_no_empty

theorem samp22_global_edge_iso_to_residualAxioms (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp22TopologyRename samp22RClosed = true ∧
      residualAxioms e = k4Axioms := by
  refine ⟨?_, residualAxioms_eq_k4 e⟩
  have h := samp22TopologySetEq_true
  simpa [topologySetEq, samp22TopologySetEq] using h

theorem samp22_fresh_g0_projects (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp22TopologyRename samp22RClosed = true ∧
      residualAxioms e = k4Axioms ∧
      ¬ samp22GProjection.gClosure.mem [] :=
  ⟨(samp22_global_edge_iso_to_residualAxioms e).1,
    (samp22_global_edge_iso_to_residualAxioms e).2,
    samp22G_no_empty_of_projection⟩

def samp22GDoc : String :=
  "fresh G₀ Closure₃ for samp22; ProjectionInclusion beyond packs/alts"

end PNPLab.Resolution
