/-
  Fresh G₀→R for hop-2 sample samp15: C_6 + chords [1, 4],[3, 5].

  Machine fact: Closure₃(G) has size 80 and excludes □; residual
  `samp15RClosed` (16) excludes □; every Closure₃(G) clause supported on
  residual edge vars lies in `samp15RClosed`.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures
import PNPLab.SampleResidualClosures

namespace PNPLab.Resolution

def samp15GAxioms : List Clause :=
  [ [(-5 : Lit), (3 : Lit)]
  , [(-3 : Lit), (5 : Lit)]
  , [(-2 : Lit), (1 : Lit)]
  , [(-1 : Lit), (2 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-4 : Lit)]
  , [(-8 : Lit), (2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (4 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-7 : Lit), (2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (5 : Lit), (6 : Lit)]
  , [(-6 : Lit), (4 : Lit), (8 : Lit)]
  , [(-6 : Lit), (5 : Lit), (7 : Lit)]
  , [(-5 : Lit), (6 : Lit), (7 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (1 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-4 : Lit), (6 : Lit), (8 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-2 : Lit), (7 : Lit), (8 : Lit)]
  , [(1 : Lit), (3 : Lit), (4 : Lit)]
  ]

def samp15GClosed : List Clause :=
  [ [(-5 : Lit), (3 : Lit)]
  , [(-3 : Lit), (5 : Lit)]
  , [(-2 : Lit), (1 : Lit)]
  , [(-1 : Lit), (2 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (-1 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-4 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-8 : Lit), (1 : Lit), (7 : Lit)]
  , [(-8 : Lit), (2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (4 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-3 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (5 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-7 : Lit), (1 : Lit), (8 : Lit)]
  , [(-7 : Lit), (2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (3 : Lit), (6 : Lit)]
  , [(-7 : Lit), (5 : Lit), (6 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (5 : Lit)]
  , [(-6 : Lit), (3 : Lit), (7 : Lit)]
  , [(-6 : Lit), (4 : Lit), (8 : Lit)]
  , [(-6 : Lit), (5 : Lit), (7 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (1 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (2 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (3 : Lit)]
  , [(-5 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-5 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-5 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-5 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-5 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-5 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (1 : Lit), (3 : Lit)]
  , [(-5 : Lit), (2 : Lit), (3 : Lit)]
  , [(-5 : Lit), (3 : Lit), (4 : Lit)]
  , [(-5 : Lit), (3 : Lit), (6 : Lit)]
  , [(-5 : Lit), (3 : Lit), (7 : Lit)]
  , [(-5 : Lit), (6 : Lit), (7 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (1 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (2 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (5 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (5 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (6 : Lit), (8 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (5 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (5 : Lit)]
  , [(-3 : Lit), (1 : Lit), (5 : Lit)]
  , [(-3 : Lit), (2 : Lit), (5 : Lit)]
  , [(-3 : Lit), (4 : Lit), (5 : Lit)]
  , [(-3 : Lit), (5 : Lit), (6 : Lit)]
  , [(-3 : Lit), (5 : Lit), (7 : Lit)]
  , [(-3 : Lit), (6 : Lit), (7 : Lit)]
  , [(-2 : Lit), (1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (1 : Lit), (4 : Lit)]
  , [(-2 : Lit), (1 : Lit), (5 : Lit)]
  , [(-2 : Lit), (1 : Lit), (7 : Lit)]
  , [(-2 : Lit), (1 : Lit), (8 : Lit)]
  , [(-2 : Lit), (7 : Lit), (8 : Lit)]
  , [(-1 : Lit), (2 : Lit), (3 : Lit)]
  , [(-1 : Lit), (2 : Lit), (4 : Lit)]
  , [(-1 : Lit), (2 : Lit), (5 : Lit)]
  , [(-1 : Lit), (2 : Lit), (7 : Lit)]
  , [(-1 : Lit), (2 : Lit), (8 : Lit)]
  , [(-1 : Lit), (7 : Lit), (8 : Lit)]
  , [(1 : Lit), (3 : Lit), (4 : Lit)]
  , [(1 : Lit), (4 : Lit), (5 : Lit)]
  , [(2 : Lit), (3 : Lit), (4 : Lit)]
  , [(2 : Lit), (4 : Lit), (5 : Lit)]
  ]

def samp15GPivots : List Lit := [-10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

def samp15GVres : List Nat := [2, 4, 5, 6, 7, 8]

theorem samp15GVres_eq_samp : samp15GVres = samp15Vres := by native_decide

def samp15GClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem samp15G_closed_bool : samp15GClosedUnder samp15GClosed 3 samp15GPivots = true := by
  native_decide

theorem samp15G_lits_in_pivots :
    (samp15GClosed.all fun C => C.all fun lit => decide (lit ∈ samp15GPivots)) = true := by
  native_decide

theorem samp15G_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ samp15GClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ samp15GPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp samp15G_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem samp15G_mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : samp15GClosedUnder S w pivots = true)
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

def samp15GClosure : WidthClosure 3 where
  axioms := samp15GAxioms
  mem := fun C => C ∈ samp15GClosed
  axiom_mem := by
    intro C hC _
    have h : (samp15GAxioms.all fun A => samp15GClosed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact samp15G_mem_of_closed samp15G_closed_bool hC hD hRes hw (samp15G_pivot hC hRes)

theorem samp15G_no_empty : ¬ samp15GClosure.mem [] := by
  simp [samp15GClosure]
  native_decide

def samp15GProjOK : Bool :=
  samp15GClosed.all fun C =>
    !(supportedOn C samp15Vres) || samp15RClosed.contains C

theorem samp15GProjOK_true : samp15GProjOK = true := by native_decide

theorem samp15G_supported_in_R
    {C : Clause} (hG : C ∈ samp15GClosed) (hsup : supportedOn C samp15Vres = true) :
    C ∈ samp15RClosed := by
  have hall := (List.all_eq_true.mp samp15GProjOK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

def samp15GProjection : ProjectionInclusion 3 where
  gClosure := samp15GClosure
  rClosure := samp15RClosure
  Vres := samp15Vres
  holds := fun _ hG hsup => samp15G_supported_in_R hG hsup

def samp15GEliminationStep : EliminationStep 3 where
  before := samp15GClosure
  after := samp15RClosure
  V_after := samp15Vres
  preserves := fun _ hB hsup => samp15G_supported_in_R hB hsup

theorem samp15G_no_empty_of_projection :
    ¬ samp15GProjection.gClosure.mem [] :=
  no_empty_of_projection samp15GProjection samp15_closure_no_empty

theorem samp15_global_edge_iso_to_residualAxioms (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp15TopologyRename samp15RClosed = true ∧
      residualAxioms e = k4Axioms := by
  refine ⟨?_, residualAxioms_eq_k4 e⟩
  have h := samp15TopologySetEq_true
  simpa [topologySetEq, samp15TopologySetEq] using h

theorem samp15_fresh_g0_projects (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp15TopologyRename samp15RClosed = true ∧
      residualAxioms e = k4Axioms ∧
      ¬ samp15GProjection.gClosure.mem [] :=
  ⟨(samp15_global_edge_iso_to_residualAxioms e).1,
    (samp15_global_edge_iso_to_residualAxioms e).2,
    samp15G_no_empty_of_projection⟩

def samp15GDoc : String :=
  "fresh G₀ Closure₃ for samp15; ProjectionInclusion beyond packs/alts"

end PNPLab.Resolution
