/-
  Fresh G₀→R for hop-3 sample samp29: C_7 + chords [0, 4],[3, 5].

  Machine fact: Closure₃(G) has size 146 and excludes □; residual
  `samp29RClosed` (16) excludes □; every Closure₃(G) clause supported on
  residual edge vars lies in `samp29RClosed`.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures
import PNPLab.SampleResidualClosures

namespace PNPLab.Resolution

def samp29GAxioms : List Clause :=
  [ [(-9 : Lit), (3 : Lit)]
  , [(-5 : Lit), (4 : Lit)]
  , [(-4 : Lit), (1 : Lit)]
  , [(-4 : Lit), (5 : Lit)]
  , [(-3 : Lit), (9 : Lit)]
  , [(-1 : Lit), (4 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (-7 : Lit)]
  , [(-9 : Lit), (7 : Lit), (8 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (2 : Lit), (6 : Lit)]
  , [(-8 : Lit), (7 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-7 : Lit), (5 : Lit), (6 : Lit)]
  , [(-7 : Lit), (8 : Lit), (9 : Lit)]
  , [(-6 : Lit), (2 : Lit), (8 : Lit)]
  , [(-6 : Lit), (5 : Lit), (7 : Lit)]
  , [(-5 : Lit), (6 : Lit), (7 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (6 : Lit), (8 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def samp29GClosed : List Clause :=
  [ [(-9 : Lit), (3 : Lit)]
  , [(-5 : Lit), (1 : Lit)]
  , [(-5 : Lit), (4 : Lit)]
  , [(-4 : Lit), (1 : Lit)]
  , [(-4 : Lit), (5 : Lit)]
  , [(-3 : Lit), (9 : Lit)]
  , [(-1 : Lit), (4 : Lit)]
  , [(-1 : Lit), (5 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (-7 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (1 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (2 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (4 : Lit)]
  , [(-9 : Lit), (-4 : Lit), (1 : Lit)]
  , [(-9 : Lit), (-4 : Lit), (2 : Lit)]
  , [(-9 : Lit), (-4 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-4 : Lit), (5 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (5 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (5 : Lit)]
  , [(-9 : Lit), (1 : Lit), (3 : Lit)]
  , [(-9 : Lit), (2 : Lit), (3 : Lit)]
  , [(-9 : Lit), (3 : Lit), (4 : Lit)]
  , [(-9 : Lit), (3 : Lit), (5 : Lit)]
  , [(-9 : Lit), (3 : Lit), (7 : Lit)]
  , [(-9 : Lit), (3 : Lit), (8 : Lit)]
  , [(-9 : Lit), (7 : Lit), (8 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (-3 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-8 : Lit), (2 : Lit), (6 : Lit)]
  , [(-8 : Lit), (3 : Lit), (7 : Lit)]
  , [(-8 : Lit), (7 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-4 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-1 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (1 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (4 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (1 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (5 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (5 : Lit)]
  , [(-7 : Lit), (1 : Lit), (6 : Lit)]
  , [(-7 : Lit), (3 : Lit), (8 : Lit)]
  , [(-7 : Lit), (4 : Lit), (6 : Lit)]
  , [(-7 : Lit), (5 : Lit), (6 : Lit)]
  , [(-7 : Lit), (8 : Lit), (9 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (1 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (4 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (1 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (5 : Lit)]
  , [(-6 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-6 : Lit), (-1 : Lit), (5 : Lit)]
  , [(-6 : Lit), (1 : Lit), (7 : Lit)]
  , [(-6 : Lit), (2 : Lit), (8 : Lit)]
  , [(-6 : Lit), (4 : Lit), (7 : Lit)]
  , [(-6 : Lit), (5 : Lit), (7 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (1 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (1 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (2 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (4 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-5 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-5 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-5 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-5 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-5 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (1 : Lit), (2 : Lit)]
  , [(-5 : Lit), (1 : Lit), (3 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (1 : Lit), (7 : Lit)]
  , [(-5 : Lit), (1 : Lit), (9 : Lit)]
  , [(-5 : Lit), (2 : Lit), (4 : Lit)]
  , [(-5 : Lit), (3 : Lit), (4 : Lit)]
  , [(-5 : Lit), (4 : Lit), (6 : Lit)]
  , [(-5 : Lit), (4 : Lit), (7 : Lit)]
  , [(-5 : Lit), (4 : Lit), (9 : Lit)]
  , [(-5 : Lit), (6 : Lit), (7 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (1 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (2 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (5 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (5 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (1 : Lit), (2 : Lit)]
  , [(-4 : Lit), (1 : Lit), (3 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (1 : Lit), (6 : Lit)]
  , [(-4 : Lit), (1 : Lit), (7 : Lit)]
  , [(-4 : Lit), (1 : Lit), (9 : Lit)]
  , [(-4 : Lit), (2 : Lit), (5 : Lit)]
  , [(-4 : Lit), (3 : Lit), (5 : Lit)]
  , [(-4 : Lit), (5 : Lit), (6 : Lit)]
  , [(-4 : Lit), (5 : Lit), (7 : Lit)]
  , [(-4 : Lit), (5 : Lit), (9 : Lit)]
  , [(-4 : Lit), (6 : Lit), (7 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (5 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (5 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-3 : Lit), (1 : Lit), (9 : Lit)]
  , [(-3 : Lit), (2 : Lit), (9 : Lit)]
  , [(-3 : Lit), (4 : Lit), (9 : Lit)]
  , [(-3 : Lit), (5 : Lit), (9 : Lit)]
  , [(-3 : Lit), (7 : Lit), (8 : Lit)]
  , [(-3 : Lit), (7 : Lit), (9 : Lit)]
  , [(-3 : Lit), (8 : Lit), (9 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (5 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-2 : Lit), (6 : Lit), (8 : Lit)]
  , [(-1 : Lit), (2 : Lit), (4 : Lit)]
  , [(-1 : Lit), (2 : Lit), (5 : Lit)]
  , [(-1 : Lit), (3 : Lit), (4 : Lit)]
  , [(-1 : Lit), (3 : Lit), (5 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(-1 : Lit), (4 : Lit), (6 : Lit)]
  , [(-1 : Lit), (4 : Lit), (7 : Lit)]
  , [(-1 : Lit), (4 : Lit), (9 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(-1 : Lit), (5 : Lit), (7 : Lit)]
  , [(-1 : Lit), (5 : Lit), (9 : Lit)]
  , [(-1 : Lit), (6 : Lit), (7 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(1 : Lit), (2 : Lit), (9 : Lit)]
  , [(2 : Lit), (3 : Lit), (4 : Lit)]
  , [(2 : Lit), (3 : Lit), (5 : Lit)]
  , [(2 : Lit), (4 : Lit), (9 : Lit)]
  , [(2 : Lit), (5 : Lit), (9 : Lit)]
  ]

def samp29GPivots : List Lit := [-11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

def samp29GVres : List Nat := [2, 4, 6, 7, 8, 9]

theorem samp29GVres_eq_samp : samp29GVres = samp29Vres := by native_decide

def samp29GClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem samp29G_closed_bool : samp29GClosedUnder samp29GClosed 3 samp29GPivots = true := by
  native_decide

theorem samp29G_lits_in_pivots :
    (samp29GClosed.all fun C => C.all fun lit => decide (lit ∈ samp29GPivots)) = true := by
  native_decide

theorem samp29G_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ samp29GClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ samp29GPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp samp29G_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem samp29G_mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : samp29GClosedUnder S w pivots = true)
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

def samp29GClosure : WidthClosure 3 where
  axioms := samp29GAxioms
  mem := fun C => C ∈ samp29GClosed
  axiom_mem := by
    intro C hC _
    have h : (samp29GAxioms.all fun A => samp29GClosed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact samp29G_mem_of_closed samp29G_closed_bool hC hD hRes hw (samp29G_pivot hC hRes)

theorem samp29G_no_empty : ¬ samp29GClosure.mem [] := by
  simp [samp29GClosure]
  native_decide

def samp29GProjOK : Bool :=
  samp29GClosed.all fun C =>
    !(supportedOn C samp29Vres) || samp29RClosed.contains C

theorem samp29GProjOK_true : samp29GProjOK = true := by native_decide

theorem samp29G_supported_in_R
    {C : Clause} (hG : C ∈ samp29GClosed) (hsup : supportedOn C samp29Vres = true) :
    C ∈ samp29RClosed := by
  have hall := (List.all_eq_true.mp samp29GProjOK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

def samp29GProjection : ProjectionInclusion 3 where
  gClosure := samp29GClosure
  rClosure := samp29RClosure
  Vres := samp29Vres
  holds := fun _ hG hsup => samp29G_supported_in_R hG hsup

def samp29GEliminationStep : EliminationStep 3 where
  before := samp29GClosure
  after := samp29RClosure
  V_after := samp29Vres
  preserves := fun _ hB hsup => samp29G_supported_in_R hB hsup

theorem samp29G_no_empty_of_projection :
    ¬ samp29GProjection.gClosure.mem [] :=
  no_empty_of_projection samp29GProjection samp29_closure_no_empty

theorem samp29_global_edge_iso_to_residualAxioms (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp29TopologyRename samp29RClosed = true ∧
      residualAxioms e = k4Axioms := by
  refine ⟨?_, residualAxioms_eq_k4 e⟩
  have h := samp29TopologySetEq_true
  simpa [topologySetEq, samp29TopologySetEq] using h

theorem samp29_fresh_g0_projects (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp29TopologyRename samp29RClosed = true ∧
      residualAxioms e = k4Axioms ∧
      ¬ samp29GProjection.gClosure.mem [] :=
  ⟨(samp29_global_edge_iso_to_residualAxioms e).1,
    (samp29_global_edge_iso_to_residualAxioms e).2,
    samp29G_no_empty_of_projection⟩

def samp29GDoc : String :=
  "fresh G₀ Closure₃ for samp29; ProjectionInclusion beyond packs/alts"

end PNPLab.Resolution
