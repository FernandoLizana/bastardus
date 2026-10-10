/-
  Fresh G₀→R for hop-3 sample samp32: C_7 + chords [0, 5],[2, 6].

  Machine fact: Closure₃(G) has size 146 and excludes □; residual
  `samp32RClosed` (16) excludes □; every Closure₃(G) clause supported on
  residual edge vars lies in `samp32RClosed`.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures
import PNPLab.SampleResidualClosures

namespace PNPLab.Resolution

def samp32GAxioms : List Clause :=
  [ [(-8 : Lit), (7 : Lit)]
  , [(-7 : Lit), (5 : Lit)]
  , [(-7 : Lit), (8 : Lit)]
  , [(-5 : Lit), (7 : Lit)]
  , [(-4 : Lit), (1 : Lit)]
  , [(-1 : Lit), (4 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (-2 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (-3 : Lit)]
  , [(-9 : Lit), (2 : Lit), (8 : Lit)]
  , [(-9 : Lit), (3 : Lit), (6 : Lit)]
  , [(-8 : Lit), (2 : Lit), (9 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-4 : Lit)]
  , [(-6 : Lit), (3 : Lit), (9 : Lit)]
  , [(-6 : Lit), (4 : Lit), (5 : Lit)]
  , [(-5 : Lit), (4 : Lit), (6 : Lit)]
  , [(-4 : Lit), (5 : Lit), (6 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (6 : Lit), (9 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (8 : Lit), (9 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def samp32GClosed : List Clause :=
  [ [(-8 : Lit), (5 : Lit)]
  , [(-8 : Lit), (7 : Lit)]
  , [(-7 : Lit), (5 : Lit)]
  , [(-7 : Lit), (8 : Lit)]
  , [(-5 : Lit), (7 : Lit)]
  , [(-5 : Lit), (8 : Lit)]
  , [(-4 : Lit), (1 : Lit)]
  , [(-1 : Lit), (4 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (-2 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (5 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (-2 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (5 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (-3 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (-2 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-9 : Lit), (2 : Lit), (5 : Lit)]
  , [(-9 : Lit), (2 : Lit), (7 : Lit)]
  , [(-9 : Lit), (2 : Lit), (8 : Lit)]
  , [(-9 : Lit), (3 : Lit), (6 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (5 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-4 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-1 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (5 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-4 : Lit), (1 : Lit)]
  , [(-8 : Lit), (-4 : Lit), (5 : Lit)]
  , [(-8 : Lit), (-4 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (5 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (5 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-8 : Lit), (1 : Lit), (5 : Lit)]
  , [(-8 : Lit), (1 : Lit), (6 : Lit)]
  , [(-8 : Lit), (1 : Lit), (7 : Lit)]
  , [(-8 : Lit), (2 : Lit), (5 : Lit)]
  , [(-8 : Lit), (2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (2 : Lit), (9 : Lit)]
  , [(-8 : Lit), (4 : Lit), (5 : Lit)]
  , [(-8 : Lit), (4 : Lit), (6 : Lit)]
  , [(-8 : Lit), (4 : Lit), (7 : Lit)]
  , [(-8 : Lit), (5 : Lit), (6 : Lit)]
  , [(-8 : Lit), (5 : Lit), (7 : Lit)]
  , [(-8 : Lit), (5 : Lit), (9 : Lit)]
  , [(-8 : Lit), (6 : Lit), (7 : Lit)]
  , [(-8 : Lit), (7 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-4 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-1 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (5 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (1 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (5 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (5 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (5 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-7 : Lit), (1 : Lit), (5 : Lit)]
  , [(-7 : Lit), (1 : Lit), (6 : Lit)]
  , [(-7 : Lit), (1 : Lit), (8 : Lit)]
  , [(-7 : Lit), (2 : Lit), (5 : Lit)]
  , [(-7 : Lit), (2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (2 : Lit), (9 : Lit)]
  , [(-7 : Lit), (4 : Lit), (5 : Lit)]
  , [(-7 : Lit), (4 : Lit), (6 : Lit)]
  , [(-7 : Lit), (4 : Lit), (8 : Lit)]
  , [(-7 : Lit), (5 : Lit), (6 : Lit)]
  , [(-7 : Lit), (5 : Lit), (8 : Lit)]
  , [(-7 : Lit), (5 : Lit), (9 : Lit)]
  , [(-7 : Lit), (6 : Lit), (8 : Lit)]
  , [(-7 : Lit), (8 : Lit), (9 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-4 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (1 : Lit)]
  , [(-6 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-6 : Lit), (1 : Lit), (5 : Lit)]
  , [(-6 : Lit), (1 : Lit), (7 : Lit)]
  , [(-6 : Lit), (1 : Lit), (8 : Lit)]
  , [(-6 : Lit), (3 : Lit), (9 : Lit)]
  , [(-6 : Lit), (4 : Lit), (5 : Lit)]
  , [(-6 : Lit), (4 : Lit), (7 : Lit)]
  , [(-6 : Lit), (4 : Lit), (8 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (1 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (7 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (8 : Lit)]
  , [(-5 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-5 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-5 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-5 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (1 : Lit), (7 : Lit)]
  , [(-5 : Lit), (1 : Lit), (8 : Lit)]
  , [(-5 : Lit), (2 : Lit), (7 : Lit)]
  , [(-5 : Lit), (2 : Lit), (8 : Lit)]
  , [(-5 : Lit), (2 : Lit), (9 : Lit)]
  , [(-5 : Lit), (4 : Lit), (6 : Lit)]
  , [(-5 : Lit), (4 : Lit), (7 : Lit)]
  , [(-5 : Lit), (4 : Lit), (8 : Lit)]
  , [(-5 : Lit), (6 : Lit), (7 : Lit)]
  , [(-5 : Lit), (6 : Lit), (8 : Lit)]
  , [(-5 : Lit), (7 : Lit), (8 : Lit)]
  , [(-5 : Lit), (7 : Lit), (9 : Lit)]
  , [(-5 : Lit), (8 : Lit), (9 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (1 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (2 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-4 : Lit), (1 : Lit), (2 : Lit)]
  , [(-4 : Lit), (1 : Lit), (3 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (1 : Lit), (6 : Lit)]
  , [(-4 : Lit), (1 : Lit), (7 : Lit)]
  , [(-4 : Lit), (1 : Lit), (8 : Lit)]
  , [(-4 : Lit), (5 : Lit), (6 : Lit)]
  , [(-4 : Lit), (6 : Lit), (7 : Lit)]
  , [(-4 : Lit), (6 : Lit), (8 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-3 : Lit), (6 : Lit), (9 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-2 : Lit), (5 : Lit), (9 : Lit)]
  , [(-2 : Lit), (7 : Lit), (9 : Lit)]
  , [(-2 : Lit), (8 : Lit), (9 : Lit)]
  , [(-1 : Lit), (2 : Lit), (4 : Lit)]
  , [(-1 : Lit), (3 : Lit), (4 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(-1 : Lit), (4 : Lit), (6 : Lit)]
  , [(-1 : Lit), (4 : Lit), (7 : Lit)]
  , [(-1 : Lit), (4 : Lit), (8 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(-1 : Lit), (6 : Lit), (7 : Lit)]
  , [(-1 : Lit), (6 : Lit), (8 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(2 : Lit), (3 : Lit), (4 : Lit)]
  ]

def samp32GPivots : List Lit := [-11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

def samp32GVres : List Nat := [2, 3, 4, 6, 7, 9]

theorem samp32GVres_eq_samp : samp32GVres = samp32Vres := by native_decide

def samp32GClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem samp32G_closed_bool : samp32GClosedUnder samp32GClosed 3 samp32GPivots = true := by
  native_decide

theorem samp32G_lits_in_pivots :
    (samp32GClosed.all fun C => C.all fun lit => decide (lit ∈ samp32GPivots)) = true := by
  native_decide

theorem samp32G_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ samp32GClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ samp32GPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp samp32G_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem samp32G_mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : samp32GClosedUnder S w pivots = true)
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

def samp32GClosure : WidthClosure 3 where
  axioms := samp32GAxioms
  mem := fun C => C ∈ samp32GClosed
  axiom_mem := by
    intro C hC _
    have h : (samp32GAxioms.all fun A => samp32GClosed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact samp32G_mem_of_closed samp32G_closed_bool hC hD hRes hw (samp32G_pivot hC hRes)

theorem samp32G_no_empty : ¬ samp32GClosure.mem [] := by
  simp [samp32GClosure]
  native_decide

def samp32GProjOK : Bool :=
  samp32GClosed.all fun C =>
    !(supportedOn C samp32Vres) || samp32RClosed.contains C

theorem samp32GProjOK_true : samp32GProjOK = true := by native_decide

theorem samp32G_supported_in_R
    {C : Clause} (hG : C ∈ samp32GClosed) (hsup : supportedOn C samp32Vres = true) :
    C ∈ samp32RClosed := by
  have hall := (List.all_eq_true.mp samp32GProjOK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

def samp32GProjection : ProjectionInclusion 3 where
  gClosure := samp32GClosure
  rClosure := samp32RClosure
  Vres := samp32Vres
  holds := fun _ hG hsup => samp32G_supported_in_R hG hsup

def samp32GEliminationStep : EliminationStep 3 where
  before := samp32GClosure
  after := samp32RClosure
  V_after := samp32Vres
  preserves := fun _ hB hsup => samp32G_supported_in_R hB hsup

theorem samp32G_no_empty_of_projection :
    ¬ samp32GProjection.gClosure.mem [] :=
  no_empty_of_projection samp32GProjection samp32_closure_no_empty

theorem samp32_global_edge_iso_to_residualAxioms (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp32TopologyRename samp32RClosed = true ∧
      residualAxioms e = k4Axioms := by
  refine ⟨?_, residualAxioms_eq_k4 e⟩
  have h := samp32TopologySetEq_true
  simpa [topologySetEq, samp32TopologySetEq] using h

theorem samp32_fresh_g0_projects (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp32TopologyRename samp32RClosed = true ∧
      residualAxioms e = k4Axioms ∧
      ¬ samp32GProjection.gClosure.mem [] :=
  ⟨(samp32_global_edge_iso_to_residualAxioms e).1,
    (samp32_global_edge_iso_to_residualAxioms e).2,
    samp32G_no_empty_of_projection⟩

def samp32GDoc : String :=
  "fresh G₀ Closure₃ for samp32; ProjectionInclusion beyond packs/alts"

end PNPLab.Resolution
