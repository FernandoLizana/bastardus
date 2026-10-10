/-
  Fresh G₀→R for hop-4 sample samp38: C_8 + chords [0, 3],[1, 5].

  Machine fact: Closure₃(G) has size 184 and excludes □; residual
  `samp38RClosed` (16) excludes □; every Closure₃(G) clause supported on
  residual edge vars lies in `samp38RClosed`.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures
import PNPLab.SampleResidualClosures

namespace PNPLab.Resolution

def samp38GAxioms : List Clause :=
  [ [(-10 : Lit), (3 : Lit)]
  , [(-10 : Lit), (9 : Lit)]
  , [(-9 : Lit), (10 : Lit)]
  , [(-8 : Lit), (7 : Lit)]
  , [(-7 : Lit), (8 : Lit)]
  , [(-6 : Lit), (4 : Lit)]
  , [(-4 : Lit), (6 : Lit)]
  , [(-3 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (-5 : Lit)]
  , [(-9 : Lit), (5 : Lit), (8 : Lit)]
  , [(-8 : Lit), (5 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-7 : Lit), (2 : Lit), (6 : Lit)]
  , [(-6 : Lit), (2 : Lit), (7 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (8 : Lit), (9 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (6 : Lit), (7 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def samp38GClosed : List Clause :=
  [ [(-10 : Lit), (3 : Lit)]
  , [(-10 : Lit), (9 : Lit)]
  , [(-9 : Lit), (3 : Lit)]
  , [(-9 : Lit), (10 : Lit)]
  , [(-8 : Lit), (7 : Lit)]
  , [(-7 : Lit), (8 : Lit)]
  , [(-6 : Lit), (4 : Lit)]
  , [(-4 : Lit), (6 : Lit)]
  , [(-3 : Lit), (9 : Lit)]
  , [(-3 : Lit), (10 : Lit)]
  , [(-10 : Lit), (-9 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-8 : Lit), (-5 : Lit)]
  , [(-10 : Lit), (-8 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-8 : Lit), (7 : Lit)]
  , [(-10 : Lit), (-8 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-7 : Lit), (-5 : Lit)]
  , [(-10 : Lit), (-7 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-7 : Lit), (8 : Lit)]
  , [(-10 : Lit), (-7 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-10 : Lit), (1 : Lit), (3 : Lit)]
  , [(-10 : Lit), (1 : Lit), (9 : Lit)]
  , [(-10 : Lit), (2 : Lit), (3 : Lit)]
  , [(-10 : Lit), (2 : Lit), (9 : Lit)]
  , [(-10 : Lit), (3 : Lit), (5 : Lit)]
  , [(-10 : Lit), (3 : Lit), (7 : Lit)]
  , [(-10 : Lit), (3 : Lit), (8 : Lit)]
  , [(-10 : Lit), (3 : Lit), (9 : Lit)]
  , [(-10 : Lit), (5 : Lit), (7 : Lit)]
  , [(-10 : Lit), (5 : Lit), (8 : Lit)]
  , [(-10 : Lit), (5 : Lit), (9 : Lit)]
  , [(-10 : Lit), (7 : Lit), (9 : Lit)]
  , [(-10 : Lit), (8 : Lit), (9 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (-5 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (-5 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-9 : Lit), (1 : Lit), (3 : Lit)]
  , [(-9 : Lit), (1 : Lit), (10 : Lit)]
  , [(-9 : Lit), (2 : Lit), (3 : Lit)]
  , [(-9 : Lit), (2 : Lit), (10 : Lit)]
  , [(-9 : Lit), (3 : Lit), (5 : Lit)]
  , [(-9 : Lit), (3 : Lit), (7 : Lit)]
  , [(-9 : Lit), (3 : Lit), (8 : Lit)]
  , [(-9 : Lit), (3 : Lit), (10 : Lit)]
  , [(-9 : Lit), (5 : Lit), (7 : Lit)]
  , [(-9 : Lit), (5 : Lit), (8 : Lit)]
  , [(-9 : Lit), (5 : Lit), (10 : Lit)]
  , [(-9 : Lit), (7 : Lit), (10 : Lit)]
  , [(-9 : Lit), (8 : Lit), (10 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (4 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (-4 : Lit), (6 : Lit)]
  , [(-8 : Lit), (-4 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (2 : Lit), (4 : Lit)]
  , [(-8 : Lit), (2 : Lit), (6 : Lit)]
  , [(-8 : Lit), (2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (3 : Lit), (5 : Lit)]
  , [(-8 : Lit), (3 : Lit), (7 : Lit)]
  , [(-8 : Lit), (4 : Lit), (7 : Lit)]
  , [(-8 : Lit), (5 : Lit), (7 : Lit)]
  , [(-8 : Lit), (5 : Lit), (9 : Lit)]
  , [(-8 : Lit), (5 : Lit), (10 : Lit)]
  , [(-8 : Lit), (6 : Lit), (7 : Lit)]
  , [(-8 : Lit), (7 : Lit), (9 : Lit)]
  , [(-8 : Lit), (7 : Lit), (10 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (4 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (2 : Lit), (4 : Lit)]
  , [(-7 : Lit), (2 : Lit), (6 : Lit)]
  , [(-7 : Lit), (2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (3 : Lit), (5 : Lit)]
  , [(-7 : Lit), (3 : Lit), (8 : Lit)]
  , [(-7 : Lit), (4 : Lit), (8 : Lit)]
  , [(-7 : Lit), (5 : Lit), (8 : Lit)]
  , [(-7 : Lit), (5 : Lit), (9 : Lit)]
  , [(-7 : Lit), (5 : Lit), (10 : Lit)]
  , [(-7 : Lit), (6 : Lit), (8 : Lit)]
  , [(-7 : Lit), (8 : Lit), (9 : Lit)]
  , [(-7 : Lit), (8 : Lit), (10 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (4 : Lit)]
  , [(-6 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-6 : Lit), (1 : Lit), (4 : Lit)]
  , [(-6 : Lit), (1 : Lit), (5 : Lit)]
  , [(-6 : Lit), (2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (2 : Lit), (7 : Lit)]
  , [(-6 : Lit), (2 : Lit), (8 : Lit)]
  , [(-6 : Lit), (4 : Lit), (5 : Lit)]
  , [(-6 : Lit), (4 : Lit), (7 : Lit)]
  , [(-6 : Lit), (4 : Lit), (8 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (6 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (3 : Lit), (7 : Lit)]
  , [(-5 : Lit), (3 : Lit), (8 : Lit)]
  , [(-5 : Lit), (7 : Lit), (9 : Lit)]
  , [(-5 : Lit), (7 : Lit), (10 : Lit)]
  , [(-5 : Lit), (8 : Lit), (9 : Lit)]
  , [(-5 : Lit), (8 : Lit), (10 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (6 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (6 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (1 : Lit), (6 : Lit)]
  , [(-4 : Lit), (2 : Lit), (6 : Lit)]
  , [(-4 : Lit), (2 : Lit), (7 : Lit)]
  , [(-4 : Lit), (2 : Lit), (8 : Lit)]
  , [(-4 : Lit), (5 : Lit), (6 : Lit)]
  , [(-4 : Lit), (6 : Lit), (7 : Lit)]
  , [(-4 : Lit), (6 : Lit), (8 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-3 : Lit), (1 : Lit), (9 : Lit)]
  , [(-3 : Lit), (1 : Lit), (10 : Lit)]
  , [(-3 : Lit), (2 : Lit), (9 : Lit)]
  , [(-3 : Lit), (2 : Lit), (10 : Lit)]
  , [(-3 : Lit), (5 : Lit), (7 : Lit)]
  , [(-3 : Lit), (5 : Lit), (8 : Lit)]
  , [(-3 : Lit), (5 : Lit), (9 : Lit)]
  , [(-3 : Lit), (5 : Lit), (10 : Lit)]
  , [(-3 : Lit), (7 : Lit), (9 : Lit)]
  , [(-3 : Lit), (7 : Lit), (10 : Lit)]
  , [(-3 : Lit), (8 : Lit), (9 : Lit)]
  , [(-3 : Lit), (8 : Lit), (10 : Lit)]
  , [(-3 : Lit), (9 : Lit), (10 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-2 : Lit), (4 : Lit), (7 : Lit)]
  , [(-2 : Lit), (4 : Lit), (8 : Lit)]
  , [(-2 : Lit), (6 : Lit), (7 : Lit)]
  , [(-2 : Lit), (6 : Lit), (8 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(1 : Lit), (2 : Lit), (9 : Lit)]
  , [(1 : Lit), (2 : Lit), (10 : Lit)]
  ]

def samp38GPivots : List Lit := [-12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

def samp38GVres : List Nat := [1, 2, 5, 6, 8, 10]

theorem samp38GVres_eq_samp : samp38GVres = samp38Vres := by native_decide

def samp38GClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem samp38G_closed_bool : samp38GClosedUnder samp38GClosed 3 samp38GPivots = true := by
  native_decide

theorem samp38G_lits_in_pivots :
    (samp38GClosed.all fun C => C.all fun lit => decide (lit ∈ samp38GPivots)) = true := by
  native_decide

theorem samp38G_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ samp38GClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ samp38GPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp samp38G_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem samp38G_mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : samp38GClosedUnder S w pivots = true)
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

def samp38GClosure : WidthClosure 3 where
  axioms := samp38GAxioms
  mem := fun C => C ∈ samp38GClosed
  axiom_mem := by
    intro C hC _
    have h : (samp38GAxioms.all fun A => samp38GClosed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact samp38G_mem_of_closed samp38G_closed_bool hC hD hRes hw (samp38G_pivot hC hRes)

theorem samp38G_no_empty : ¬ samp38GClosure.mem [] := by
  simp [samp38GClosure]
  native_decide

def samp38GProjOK : Bool :=
  samp38GClosed.all fun C =>
    !(supportedOn C samp38Vres) || samp38RClosed.contains C

theorem samp38GProjOK_true : samp38GProjOK = true := by native_decide

theorem samp38G_supported_in_R
    {C : Clause} (hG : C ∈ samp38GClosed) (hsup : supportedOn C samp38Vres = true) :
    C ∈ samp38RClosed := by
  have hall := (List.all_eq_true.mp samp38GProjOK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

def samp38GProjection : ProjectionInclusion 3 where
  gClosure := samp38GClosure
  rClosure := samp38RClosure
  Vres := samp38Vres
  holds := fun _ hG hsup => samp38G_supported_in_R hG hsup

def samp38GEliminationStep : EliminationStep 3 where
  before := samp38GClosure
  after := samp38RClosure
  V_after := samp38Vres
  preserves := fun _ hB hsup => samp38G_supported_in_R hB hsup

theorem samp38G_no_empty_of_projection :
    ¬ samp38GProjection.gClosure.mem [] :=
  no_empty_of_projection samp38GProjection samp38_closure_no_empty

theorem samp38_global_edge_iso_to_residualAxioms (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp38TopologyRename samp38RClosed = true ∧
      residualAxioms e = k4Axioms := by
  refine ⟨?_, residualAxioms_eq_k4 e⟩
  have h := samp38TopologySetEq_true
  simpa [topologySetEq, samp38TopologySetEq] using h

theorem samp38_fresh_g0_projects (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp38TopologyRename samp38RClosed = true ∧
      residualAxioms e = k4Axioms ∧
      ¬ samp38GProjection.gClosure.mem [] :=
  ⟨(samp38_global_edge_iso_to_residualAxioms e).1,
    (samp38_global_edge_iso_to_residualAxioms e).2,
    samp38G_no_empty_of_projection⟩

def samp38GDoc : String :=
  "fresh G₀ Closure₃ for samp38; ProjectionInclusion beyond packs/alts"

end PNPLab.Resolution
