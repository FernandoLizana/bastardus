/-
  Fresh G₀→R for hop-4 sample samp37: C_8 + chords [0, 3],[1, 4].

  Machine fact: Closure₃(G) has size 198 and excludes □; residual
  `samp37RClosed` (16) excludes □; every Closure₃(G) clause supported on
  residual edge vars lies in `samp37RClosed`.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures
import PNPLab.SampleResidualClosures

namespace PNPLab.Resolution

def samp37GAxioms : List Clause :=
  [ [(-10 : Lit), (3 : Lit)]
  , [(-10 : Lit), (9 : Lit)]
  , [(-9 : Lit), (8 : Lit)]
  , [(-9 : Lit), (10 : Lit)]
  , [(-8 : Lit), (9 : Lit)]
  , [(-6 : Lit), (4 : Lit)]
  , [(-4 : Lit), (6 : Lit)]
  , [(-3 : Lit), (10 : Lit)]
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

def samp37GClosed : List Clause :=
  [ [(-10 : Lit), (3 : Lit)]
  , [(-10 : Lit), (8 : Lit)]
  , [(-10 : Lit), (9 : Lit)]
  , [(-9 : Lit), (3 : Lit)]
  , [(-9 : Lit), (8 : Lit)]
  , [(-9 : Lit), (10 : Lit)]
  , [(-8 : Lit), (3 : Lit)]
  , [(-8 : Lit), (9 : Lit)]
  , [(-8 : Lit), (10 : Lit)]
  , [(-6 : Lit), (4 : Lit)]
  , [(-4 : Lit), (6 : Lit)]
  , [(-3 : Lit), (8 : Lit)]
  , [(-3 : Lit), (9 : Lit)]
  , [(-3 : Lit), (10 : Lit)]
  , [(-10 : Lit), (-9 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-9 : Lit), (8 : Lit)]
  , [(-10 : Lit), (-8 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-8 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-7 : Lit), (-5 : Lit)]
  , [(-10 : Lit), (-7 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-7 : Lit), (8 : Lit)]
  , [(-10 : Lit), (-7 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-10 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-10 : Lit), (1 : Lit), (3 : Lit)]
  , [(-10 : Lit), (1 : Lit), (8 : Lit)]
  , [(-10 : Lit), (1 : Lit), (9 : Lit)]
  , [(-10 : Lit), (2 : Lit), (3 : Lit)]
  , [(-10 : Lit), (2 : Lit), (8 : Lit)]
  , [(-10 : Lit), (2 : Lit), (9 : Lit)]
  , [(-10 : Lit), (3 : Lit), (5 : Lit)]
  , [(-10 : Lit), (3 : Lit), (7 : Lit)]
  , [(-10 : Lit), (3 : Lit), (8 : Lit)]
  , [(-10 : Lit), (3 : Lit), (9 : Lit)]
  , [(-10 : Lit), (5 : Lit), (7 : Lit)]
  , [(-10 : Lit), (5 : Lit), (8 : Lit)]
  , [(-10 : Lit), (5 : Lit), (9 : Lit)]
  , [(-10 : Lit), (7 : Lit), (8 : Lit)]
  , [(-10 : Lit), (7 : Lit), (9 : Lit)]
  , [(-10 : Lit), (8 : Lit), (9 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (-5 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-9 : Lit), (1 : Lit), (3 : Lit)]
  , [(-9 : Lit), (1 : Lit), (8 : Lit)]
  , [(-9 : Lit), (1 : Lit), (10 : Lit)]
  , [(-9 : Lit), (2 : Lit), (3 : Lit)]
  , [(-9 : Lit), (2 : Lit), (8 : Lit)]
  , [(-9 : Lit), (2 : Lit), (10 : Lit)]
  , [(-9 : Lit), (3 : Lit), (5 : Lit)]
  , [(-9 : Lit), (3 : Lit), (7 : Lit)]
  , [(-9 : Lit), (3 : Lit), (8 : Lit)]
  , [(-9 : Lit), (3 : Lit), (10 : Lit)]
  , [(-9 : Lit), (5 : Lit), (7 : Lit)]
  , [(-9 : Lit), (5 : Lit), (8 : Lit)]
  , [(-9 : Lit), (5 : Lit), (10 : Lit)]
  , [(-9 : Lit), (7 : Lit), (8 : Lit)]
  , [(-9 : Lit), (7 : Lit), (10 : Lit)]
  , [(-9 : Lit), (8 : Lit), (10 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (-5 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (10 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (10 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-8 : Lit), (1 : Lit), (3 : Lit)]
  , [(-8 : Lit), (1 : Lit), (9 : Lit)]
  , [(-8 : Lit), (1 : Lit), (10 : Lit)]
  , [(-8 : Lit), (2 : Lit), (3 : Lit)]
  , [(-8 : Lit), (2 : Lit), (9 : Lit)]
  , [(-8 : Lit), (2 : Lit), (10 : Lit)]
  , [(-8 : Lit), (3 : Lit), (5 : Lit)]
  , [(-8 : Lit), (3 : Lit), (7 : Lit)]
  , [(-8 : Lit), (3 : Lit), (9 : Lit)]
  , [(-8 : Lit), (3 : Lit), (10 : Lit)]
  , [(-8 : Lit), (5 : Lit), (7 : Lit)]
  , [(-8 : Lit), (5 : Lit), (9 : Lit)]
  , [(-8 : Lit), (5 : Lit), (10 : Lit)]
  , [(-8 : Lit), (7 : Lit), (9 : Lit)]
  , [(-8 : Lit), (7 : Lit), (10 : Lit)]
  , [(-8 : Lit), (9 : Lit), (10 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (4 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-7 : Lit), (2 : Lit), (4 : Lit)]
  , [(-7 : Lit), (2 : Lit), (6 : Lit)]
  , [(-7 : Lit), (3 : Lit), (5 : Lit)]
  , [(-7 : Lit), (5 : Lit), (8 : Lit)]
  , [(-7 : Lit), (5 : Lit), (9 : Lit)]
  , [(-7 : Lit), (5 : Lit), (10 : Lit)]
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
  , [(-5 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (3 : Lit), (7 : Lit)]
  , [(-5 : Lit), (7 : Lit), (8 : Lit)]
  , [(-5 : Lit), (7 : Lit), (9 : Lit)]
  , [(-5 : Lit), (7 : Lit), (10 : Lit)]
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
  , [(-3 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-3 : Lit), (1 : Lit), (8 : Lit)]
  , [(-3 : Lit), (1 : Lit), (9 : Lit)]
  , [(-3 : Lit), (1 : Lit), (10 : Lit)]
  , [(-3 : Lit), (2 : Lit), (8 : Lit)]
  , [(-3 : Lit), (2 : Lit), (9 : Lit)]
  , [(-3 : Lit), (2 : Lit), (10 : Lit)]
  , [(-3 : Lit), (5 : Lit), (7 : Lit)]
  , [(-3 : Lit), (5 : Lit), (8 : Lit)]
  , [(-3 : Lit), (5 : Lit), (9 : Lit)]
  , [(-3 : Lit), (5 : Lit), (10 : Lit)]
  , [(-3 : Lit), (7 : Lit), (8 : Lit)]
  , [(-3 : Lit), (7 : Lit), (9 : Lit)]
  , [(-3 : Lit), (7 : Lit), (10 : Lit)]
  , [(-3 : Lit), (8 : Lit), (9 : Lit)]
  , [(-3 : Lit), (8 : Lit), (10 : Lit)]
  , [(-3 : Lit), (9 : Lit), (10 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-2 : Lit), (4 : Lit), (7 : Lit)]
  , [(-2 : Lit), (6 : Lit), (7 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(1 : Lit), (2 : Lit), (8 : Lit)]
  , [(1 : Lit), (2 : Lit), (9 : Lit)]
  , [(1 : Lit), (2 : Lit), (10 : Lit)]
  ]

def samp37GPivots : List Lit := [-12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

def samp37GVres : List Nat := [1, 2, 5, 6, 7, 9]

theorem samp37GVres_eq_samp : samp37GVres = samp37Vres := by native_decide

def samp37GClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem samp37G_closed_bool : samp37GClosedUnder samp37GClosed 3 samp37GPivots = true := by
  native_decide

theorem samp37G_lits_in_pivots :
    (samp37GClosed.all fun C => C.all fun lit => decide (lit ∈ samp37GPivots)) = true := by
  native_decide

theorem samp37G_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ samp37GClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ samp37GPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp samp37G_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem samp37G_mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : samp37GClosedUnder S w pivots = true)
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

def samp37GClosure : WidthClosure 3 where
  axioms := samp37GAxioms
  mem := fun C => C ∈ samp37GClosed
  axiom_mem := by
    intro C hC _
    have h : (samp37GAxioms.all fun A => samp37GClosed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact samp37G_mem_of_closed samp37G_closed_bool hC hD hRes hw (samp37G_pivot hC hRes)

theorem samp37G_no_empty : ¬ samp37GClosure.mem [] := by
  simp [samp37GClosure]
  native_decide

def samp37GProjOK : Bool :=
  samp37GClosed.all fun C =>
    !(supportedOn C samp37Vres) || samp37RClosed.contains C

theorem samp37GProjOK_true : samp37GProjOK = true := by native_decide

theorem samp37G_supported_in_R
    {C : Clause} (hG : C ∈ samp37GClosed) (hsup : supportedOn C samp37Vres = true) :
    C ∈ samp37RClosed := by
  have hall := (List.all_eq_true.mp samp37GProjOK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

def samp37GProjection : ProjectionInclusion 3 where
  gClosure := samp37GClosure
  rClosure := samp37RClosure
  Vres := samp37Vres
  holds := fun _ hG hsup => samp37G_supported_in_R hG hsup

def samp37GEliminationStep : EliminationStep 3 where
  before := samp37GClosure
  after := samp37RClosure
  V_after := samp37Vres
  preserves := fun _ hB hsup => samp37G_supported_in_R hB hsup

theorem samp37G_no_empty_of_projection :
    ¬ samp37GProjection.gClosure.mem [] :=
  no_empty_of_projection samp37GProjection samp37_closure_no_empty

theorem samp37_global_edge_iso_to_residualAxioms (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp37TopologyRename samp37RClosed = true ∧
      residualAxioms e = k4Axioms := by
  refine ⟨?_, residualAxioms_eq_k4 e⟩
  have h := samp37TopologySetEq_true
  simpa [topologySetEq, samp37TopologySetEq] using h

theorem samp37_fresh_g0_projects (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp37TopologyRename samp37RClosed = true ∧
      residualAxioms e = k4Axioms ∧
      ¬ samp37GProjection.gClosure.mem [] :=
  ⟨(samp37_global_edge_iso_to_residualAxioms e).1,
    (samp37_global_edge_iso_to_residualAxioms e).2,
    samp37G_no_empty_of_projection⟩

def samp37GDoc : String :=
  "fresh G₀ Closure₃ for samp37; ProjectionInclusion beyond packs/alts"

end PNPLab.Resolution
