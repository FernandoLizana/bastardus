/-
  Fresh G₀→R for hop-2 sample samp4: C_6 + chords [0, 2],[1, 4].

  Machine fact: Closure₃(G) has size 80 and excludes □; residual
  `samp4RClosed` (16) excludes □; every Closure₃(G) clause supported on
  residual edge vars lies in `samp4RClosed`.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures
import PNPLab.SampleResidualClosures

namespace PNPLab.Resolution

def samp4GAxioms : List Clause :=
  [ [(-8 : Lit), (3 : Lit)]
  , [(-7 : Lit), (6 : Lit)]
  , [(-6 : Lit), (7 : Lit)]
  , [(-3 : Lit), (8 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (-5 : Lit)]
  , [(-8 : Lit), (5 : Lit), (7 : Lit)]
  , [(-7 : Lit), (5 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-6 : Lit), (2 : Lit), (4 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (7 : Lit), (8 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (2 : Lit), (6 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (4 : Lit), (6 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def samp4GClosed : List Clause :=
  [ [(-8 : Lit), (3 : Lit)]
  , [(-7 : Lit), (6 : Lit)]
  , [(-6 : Lit), (7 : Lit)]
  , [(-3 : Lit), (8 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (-5 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (6 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-8 : Lit), (1 : Lit), (3 : Lit)]
  , [(-8 : Lit), (2 : Lit), (3 : Lit)]
  , [(-8 : Lit), (3 : Lit), (5 : Lit)]
  , [(-8 : Lit), (3 : Lit), (6 : Lit)]
  , [(-8 : Lit), (3 : Lit), (7 : Lit)]
  , [(-8 : Lit), (5 : Lit), (6 : Lit)]
  , [(-8 : Lit), (5 : Lit), (7 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (6 : Lit)]
  , [(-7 : Lit), (2 : Lit), (4 : Lit)]
  , [(-7 : Lit), (2 : Lit), (6 : Lit)]
  , [(-7 : Lit), (3 : Lit), (5 : Lit)]
  , [(-7 : Lit), (3 : Lit), (6 : Lit)]
  , [(-7 : Lit), (4 : Lit), (6 : Lit)]
  , [(-7 : Lit), (5 : Lit), (6 : Lit)]
  , [(-7 : Lit), (5 : Lit), (8 : Lit)]
  , [(-7 : Lit), (6 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-6 : Lit), (2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (2 : Lit), (7 : Lit)]
  , [(-6 : Lit), (3 : Lit), (5 : Lit)]
  , [(-6 : Lit), (3 : Lit), (7 : Lit)]
  , [(-6 : Lit), (4 : Lit), (7 : Lit)]
  , [(-6 : Lit), (5 : Lit), (7 : Lit)]
  , [(-6 : Lit), (5 : Lit), (8 : Lit)]
  , [(-6 : Lit), (7 : Lit), (8 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (3 : Lit), (6 : Lit)]
  , [(-5 : Lit), (3 : Lit), (7 : Lit)]
  , [(-5 : Lit), (6 : Lit), (8 : Lit)]
  , [(-5 : Lit), (7 : Lit), (8 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (2 : Lit), (6 : Lit)]
  , [(-4 : Lit), (2 : Lit), (7 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-3 : Lit), (1 : Lit), (8 : Lit)]
  , [(-3 : Lit), (2 : Lit), (8 : Lit)]
  , [(-3 : Lit), (5 : Lit), (6 : Lit)]
  , [(-3 : Lit), (5 : Lit), (7 : Lit)]
  , [(-3 : Lit), (5 : Lit), (8 : Lit)]
  , [(-3 : Lit), (6 : Lit), (8 : Lit)]
  , [(-3 : Lit), (7 : Lit), (8 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-2 : Lit), (4 : Lit), (6 : Lit)]
  , [(-2 : Lit), (4 : Lit), (7 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(1 : Lit), (2 : Lit), (8 : Lit)]
  ]

def samp4GPivots : List Lit := [-10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

def samp4GVres : List Nat := [1, 2, 4, 5, 7, 8]

theorem samp4GVres_eq_samp : samp4GVres = samp4Vres := by native_decide

def samp4GClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem samp4G_closed_bool : samp4GClosedUnder samp4GClosed 3 samp4GPivots = true := by
  native_decide

theorem samp4G_lits_in_pivots :
    (samp4GClosed.all fun C => C.all fun lit => decide (lit ∈ samp4GPivots)) = true := by
  native_decide

theorem samp4G_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ samp4GClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ samp4GPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp samp4G_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem samp4G_mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : samp4GClosedUnder S w pivots = true)
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

def samp4GClosure : WidthClosure 3 where
  axioms := samp4GAxioms
  mem := fun C => C ∈ samp4GClosed
  axiom_mem := by
    intro C hC _
    have h : (samp4GAxioms.all fun A => samp4GClosed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact samp4G_mem_of_closed samp4G_closed_bool hC hD hRes hw (samp4G_pivot hC hRes)

theorem samp4G_no_empty : ¬ samp4GClosure.mem [] := by
  simp [samp4GClosure]
  native_decide

def samp4GProjOK : Bool :=
  samp4GClosed.all fun C =>
    !(supportedOn C samp4Vres) || samp4RClosed.contains C

theorem samp4GProjOK_true : samp4GProjOK = true := by native_decide

theorem samp4G_supported_in_R
    {C : Clause} (hG : C ∈ samp4GClosed) (hsup : supportedOn C samp4Vres = true) :
    C ∈ samp4RClosed := by
  have hall := (List.all_eq_true.mp samp4GProjOK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

def samp4GProjection : ProjectionInclusion 3 where
  gClosure := samp4GClosure
  rClosure := samp4RClosure
  Vres := samp4Vres
  holds := fun _ hG hsup => samp4G_supported_in_R hG hsup

def samp4GEliminationStep : EliminationStep 3 where
  before := samp4GClosure
  after := samp4RClosure
  V_after := samp4Vres
  preserves := fun _ hB hsup => samp4G_supported_in_R hB hsup

theorem samp4G_no_empty_of_projection :
    ¬ samp4GProjection.gClosure.mem [] :=
  no_empty_of_projection samp4GProjection samp4_closure_no_empty

theorem samp4_global_edge_iso_to_residualAxioms (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp4TopologyRename samp4RClosed = true ∧
      residualAxioms e = k4Axioms := by
  refine ⟨?_, residualAxioms_eq_k4 e⟩
  have h := samp4TopologySetEq_true
  simpa [topologySetEq, samp4TopologySetEq] using h

theorem samp4_fresh_g0_projects (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp4TopologyRename samp4RClosed = true ∧
      residualAxioms e = k4Axioms ∧
      ¬ samp4GProjection.gClosure.mem [] :=
  ⟨(samp4_global_edge_iso_to_residualAxioms e).1,
    (samp4_global_edge_iso_to_residualAxioms e).2,
    samp4G_no_empty_of_projection⟩

def samp4GDoc : String :=
  "fresh G₀ Closure₃ for samp4; ProjectionInclusion beyond packs/alts"

end PNPLab.Resolution
