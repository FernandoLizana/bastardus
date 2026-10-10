/-
  Fresh G₀→R for hop-1 sample samp3: C_5 + chords [1, 3],[2, 4].

  Machine fact: Closure₃(G) has size 42 and excludes □; residual
  `samp3RClosed` (16) excludes □; every Closure₃(G) clause supported on
  residual edge vars lies in `samp3RClosed`.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures
import PNPLab.SampleResidualClosures

namespace PNPLab.Resolution

def samp3GAxioms : List Clause :=
  [ [(-2 : Lit), (1 : Lit)]
  , [(-1 : Lit), (2 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (-4 : Lit)]
  , [(-7 : Lit), (2 : Lit), (6 : Lit)]
  , [(-7 : Lit), (4 : Lit), (5 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-6 : Lit), (2 : Lit), (7 : Lit)]
  , [(-6 : Lit), (3 : Lit), (5 : Lit)]
  , [(-5 : Lit), (3 : Lit), (6 : Lit)]
  , [(-5 : Lit), (4 : Lit), (7 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (1 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-4 : Lit), (5 : Lit), (7 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-3 : Lit), (5 : Lit), (6 : Lit)]
  , [(-2 : Lit), (6 : Lit), (7 : Lit)]
  , [(1 : Lit), (3 : Lit), (4 : Lit)]
  ]

def samp3GClosed : List Clause :=
  [ [(-2 : Lit), (1 : Lit)]
  , [(-1 : Lit), (2 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-1 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (-4 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-7 : Lit), (1 : Lit), (6 : Lit)]
  , [(-7 : Lit), (2 : Lit), (6 : Lit)]
  , [(-7 : Lit), (4 : Lit), (5 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-6 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-6 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-6 : Lit), (1 : Lit), (7 : Lit)]
  , [(-6 : Lit), (2 : Lit), (7 : Lit)]
  , [(-6 : Lit), (3 : Lit), (5 : Lit)]
  , [(-5 : Lit), (3 : Lit), (6 : Lit)]
  , [(-5 : Lit), (4 : Lit), (7 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (1 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (2 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-4 : Lit), (5 : Lit), (7 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-3 : Lit), (5 : Lit), (6 : Lit)]
  , [(-2 : Lit), (1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (1 : Lit), (4 : Lit)]
  , [(-2 : Lit), (1 : Lit), (6 : Lit)]
  , [(-2 : Lit), (1 : Lit), (7 : Lit)]
  , [(-2 : Lit), (6 : Lit), (7 : Lit)]
  , [(-1 : Lit), (2 : Lit), (3 : Lit)]
  , [(-1 : Lit), (2 : Lit), (4 : Lit)]
  , [(-1 : Lit), (2 : Lit), (6 : Lit)]
  , [(-1 : Lit), (2 : Lit), (7 : Lit)]
  , [(-1 : Lit), (6 : Lit), (7 : Lit)]
  , [(1 : Lit), (3 : Lit), (4 : Lit)]
  , [(2 : Lit), (3 : Lit), (4 : Lit)]
  ]

def samp3GPivots : List Lit := [-10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

def samp3GVres : List Nat := [2, 3, 4, 5, 6, 7]

theorem samp3GVres_eq_samp : samp3GVres = samp3Vres := by native_decide

def samp3GClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem samp3G_closed_bool : samp3GClosedUnder samp3GClosed 3 samp3GPivots = true := by
  native_decide

theorem samp3G_lits_in_pivots :
    (samp3GClosed.all fun C => C.all fun lit => decide (lit ∈ samp3GPivots)) = true := by
  native_decide

theorem samp3G_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ samp3GClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ samp3GPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp samp3G_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem samp3G_mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : samp3GClosedUnder S w pivots = true)
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

def samp3GClosure : WidthClosure 3 where
  axioms := samp3GAxioms
  mem := fun C => C ∈ samp3GClosed
  axiom_mem := by
    intro C hC _
    have h : (samp3GAxioms.all fun A => samp3GClosed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact samp3G_mem_of_closed samp3G_closed_bool hC hD hRes hw (samp3G_pivot hC hRes)

theorem samp3G_no_empty : ¬ samp3GClosure.mem [] := by
  simp [samp3GClosure]
  native_decide

def samp3GProjOK : Bool :=
  samp3GClosed.all fun C =>
    !(supportedOn C samp3Vres) || samp3RClosed.contains C

theorem samp3GProjOK_true : samp3GProjOK = true := by native_decide

theorem samp3G_supported_in_R
    {C : Clause} (hG : C ∈ samp3GClosed) (hsup : supportedOn C samp3Vres = true) :
    C ∈ samp3RClosed := by
  have hall := (List.all_eq_true.mp samp3GProjOK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

def samp3GProjection : ProjectionInclusion 3 where
  gClosure := samp3GClosure
  rClosure := samp3RClosure
  Vres := samp3Vres
  holds := fun _ hG hsup => samp3G_supported_in_R hG hsup

def samp3GEliminationStep : EliminationStep 3 where
  before := samp3GClosure
  after := samp3RClosure
  V_after := samp3Vres
  preserves := fun _ hB hsup => samp3G_supported_in_R hB hsup

theorem samp3G_no_empty_of_projection :
    ¬ samp3GProjection.gClosure.mem [] :=
  no_empty_of_projection samp3GProjection samp3_closure_no_empty

theorem samp3_global_edge_iso_to_residualAxioms (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp3TopologyRename samp3RClosed = true ∧
      residualAxioms e = k4Axioms := by
  refine ⟨?_, residualAxioms_eq_k4 e⟩
  have h := samp3TopologySetEq_true
  simpa [topologySetEq, samp3TopologySetEq] using h

theorem samp3_fresh_g0_projects (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp3TopologyRename samp3RClosed = true ∧
      residualAxioms e = k4Axioms ∧
      ¬ samp3GProjection.gClosure.mem [] :=
  ⟨(samp3_global_edge_iso_to_residualAxioms e).1,
    (samp3_global_edge_iso_to_residualAxioms e).2,
    samp3G_no_empty_of_projection⟩

def samp3GDoc : String :=
  "fresh G₀ Closure₃ for samp3; ProjectionInclusion beyond packs/alts"

end PNPLab.Resolution
