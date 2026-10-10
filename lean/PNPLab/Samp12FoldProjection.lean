/-
  Fresh G₀→R for hop-2 sample samp12: C_6 + chords [1, 3],[2, 4].

  Machine fact: Closure₃(G) has size 92 and excludes □; residual
  `samp12RClosed` (16) excludes □; every Closure₃(G) clause supported on
  residual edge vars lies in `samp12RClosed`.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures
import PNPLab.SampleResidualClosures

namespace PNPLab.Resolution

def samp12GAxioms : List Clause :=
  [ [(-8 : Lit), (2 : Lit)]
  , [(-2 : Lit), (1 : Lit)]
  , [(-2 : Lit), (8 : Lit)]
  , [(-1 : Lit), (2 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (-6 : Lit)]
  , [(-8 : Lit), (6 : Lit), (7 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (-4 : Lit)]
  , [(-7 : Lit), (4 : Lit), (5 : Lit)]
  , [(-7 : Lit), (6 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-6 : Lit), (3 : Lit), (5 : Lit)]
  , [(-6 : Lit), (7 : Lit), (8 : Lit)]
  , [(-5 : Lit), (3 : Lit), (6 : Lit)]
  , [(-5 : Lit), (4 : Lit), (7 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (1 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-4 : Lit), (5 : Lit), (7 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-3 : Lit), (5 : Lit), (6 : Lit)]
  , [(1 : Lit), (3 : Lit), (4 : Lit)]
  ]

def samp12GClosed : List Clause :=
  [ [(-8 : Lit), (1 : Lit)]
  , [(-8 : Lit), (2 : Lit)]
  , [(-2 : Lit), (1 : Lit)]
  , [(-2 : Lit), (8 : Lit)]
  , [(-1 : Lit), (2 : Lit)]
  , [(-1 : Lit), (8 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (-6 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (1 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (2 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (1 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (2 : Lit)]
  , [(-8 : Lit), (-4 : Lit), (1 : Lit)]
  , [(-8 : Lit), (-4 : Lit), (2 : Lit)]
  , [(-8 : Lit), (-4 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (1 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (2 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (4 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-8 : Lit), (1 : Lit), (2 : Lit)]
  , [(-8 : Lit), (1 : Lit), (3 : Lit)]
  , [(-8 : Lit), (1 : Lit), (4 : Lit)]
  , [(-8 : Lit), (1 : Lit), (6 : Lit)]
  , [(-8 : Lit), (1 : Lit), (7 : Lit)]
  , [(-8 : Lit), (2 : Lit), (3 : Lit)]
  , [(-8 : Lit), (2 : Lit), (4 : Lit)]
  , [(-8 : Lit), (2 : Lit), (6 : Lit)]
  , [(-8 : Lit), (2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (6 : Lit), (7 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-1 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (-4 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-7 : Lit), (1 : Lit), (6 : Lit)]
  , [(-7 : Lit), (2 : Lit), (6 : Lit)]
  , [(-7 : Lit), (4 : Lit), (5 : Lit)]
  , [(-7 : Lit), (6 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-6 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-6 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-6 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-6 : Lit), (1 : Lit), (7 : Lit)]
  , [(-6 : Lit), (2 : Lit), (7 : Lit)]
  , [(-6 : Lit), (3 : Lit), (5 : Lit)]
  , [(-6 : Lit), (7 : Lit), (8 : Lit)]
  , [(-5 : Lit), (3 : Lit), (6 : Lit)]
  , [(-5 : Lit), (4 : Lit), (7 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (1 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (2 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-4 : Lit), (5 : Lit), (7 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-3 : Lit), (5 : Lit), (6 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-2 : Lit), (1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (1 : Lit), (4 : Lit)]
  , [(-2 : Lit), (1 : Lit), (6 : Lit)]
  , [(-2 : Lit), (1 : Lit), (7 : Lit)]
  , [(-2 : Lit), (1 : Lit), (8 : Lit)]
  , [(-2 : Lit), (3 : Lit), (8 : Lit)]
  , [(-2 : Lit), (4 : Lit), (8 : Lit)]
  , [(-2 : Lit), (6 : Lit), (7 : Lit)]
  , [(-2 : Lit), (6 : Lit), (8 : Lit)]
  , [(-2 : Lit), (7 : Lit), (8 : Lit)]
  , [(-1 : Lit), (2 : Lit), (3 : Lit)]
  , [(-1 : Lit), (2 : Lit), (4 : Lit)]
  , [(-1 : Lit), (2 : Lit), (6 : Lit)]
  , [(-1 : Lit), (2 : Lit), (7 : Lit)]
  , [(-1 : Lit), (2 : Lit), (8 : Lit)]
  , [(-1 : Lit), (3 : Lit), (8 : Lit)]
  , [(-1 : Lit), (4 : Lit), (8 : Lit)]
  , [(-1 : Lit), (6 : Lit), (7 : Lit)]
  , [(-1 : Lit), (6 : Lit), (8 : Lit)]
  , [(-1 : Lit), (7 : Lit), (8 : Lit)]
  , [(1 : Lit), (3 : Lit), (4 : Lit)]
  , [(2 : Lit), (3 : Lit), (4 : Lit)]
  , [(3 : Lit), (4 : Lit), (8 : Lit)]
  ]

def samp12GPivots : List Lit := [-10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

def samp12GVres : List Nat := [3, 4, 5, 6, 7, 8]

theorem samp12GVres_eq_samp : samp12GVres = samp12Vres := by native_decide

def samp12GClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem samp12G_closed_bool : samp12GClosedUnder samp12GClosed 3 samp12GPivots = true := by
  native_decide

theorem samp12G_lits_in_pivots :
    (samp12GClosed.all fun C => C.all fun lit => decide (lit ∈ samp12GPivots)) = true := by
  native_decide

theorem samp12G_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ samp12GClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ samp12GPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp samp12G_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem samp12G_mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : samp12GClosedUnder S w pivots = true)
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

def samp12GClosure : WidthClosure 3 where
  axioms := samp12GAxioms
  mem := fun C => C ∈ samp12GClosed
  axiom_mem := by
    intro C hC _
    have h : (samp12GAxioms.all fun A => samp12GClosed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact samp12G_mem_of_closed samp12G_closed_bool hC hD hRes hw (samp12G_pivot hC hRes)

theorem samp12G_no_empty : ¬ samp12GClosure.mem [] := by
  simp [samp12GClosure]
  native_decide

def samp12GProjOK : Bool :=
  samp12GClosed.all fun C =>
    !(supportedOn C samp12Vres) || samp12RClosed.contains C

theorem samp12GProjOK_true : samp12GProjOK = true := by native_decide

theorem samp12G_supported_in_R
    {C : Clause} (hG : C ∈ samp12GClosed) (hsup : supportedOn C samp12Vres = true) :
    C ∈ samp12RClosed := by
  have hall := (List.all_eq_true.mp samp12GProjOK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

def samp12GProjection : ProjectionInclusion 3 where
  gClosure := samp12GClosure
  rClosure := samp12RClosure
  Vres := samp12Vres
  holds := fun _ hG hsup => samp12G_supported_in_R hG hsup

def samp12GEliminationStep : EliminationStep 3 where
  before := samp12GClosure
  after := samp12RClosure
  V_after := samp12Vres
  preserves := fun _ hB hsup => samp12G_supported_in_R hB hsup

theorem samp12G_no_empty_of_projection :
    ¬ samp12GProjection.gClosure.mem [] :=
  no_empty_of_projection samp12GProjection samp12_closure_no_empty

theorem samp12_global_edge_iso_to_residualAxioms (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp12TopologyRename samp12RClosed = true ∧
      residualAxioms e = k4Axioms := by
  refine ⟨?_, residualAxioms_eq_k4 e⟩
  have h := samp12TopologySetEq_true
  simpa [topologySetEq, samp12TopologySetEq] using h

theorem samp12_fresh_g0_projects (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp12TopologyRename samp12RClosed = true ∧
      residualAxioms e = k4Axioms ∧
      ¬ samp12GProjection.gClosure.mem [] :=
  ⟨(samp12_global_edge_iso_to_residualAxioms e).1,
    (samp12_global_edge_iso_to_residualAxioms e).2,
    samp12G_no_empty_of_projection⟩

def samp12GDoc : String :=
  "fresh G₀ Closure₃ for samp12; ProjectionInclusion beyond packs/alts"

end PNPLab.Resolution
