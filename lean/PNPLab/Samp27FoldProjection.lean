/-
  Fresh G₀→R for hop-3 sample samp27: C_7 + chords [0, 4],[2, 5].

  Machine fact: Closure₃(G) has size 118 and excludes □; residual
  `samp27RClosed` (16) excludes □; every Closure₃(G) clause supported on
  residual edge vars lies in `samp27RClosed`.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures
import PNPLab.SampleResidualClosures

namespace PNPLab.Resolution

def samp27GAxioms : List Clause :=
  [ [(-9 : Lit), (3 : Lit)]
  , [(-7 : Lit), (5 : Lit)]
  , [(-5 : Lit), (7 : Lit)]
  , [(-4 : Lit), (1 : Lit)]
  , [(-3 : Lit), (9 : Lit)]
  , [(-1 : Lit), (4 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (-6 : Lit)]
  , [(-9 : Lit), (6 : Lit), (8 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (6 : Lit), (9 : Lit)]
  , [(-7 : Lit), (2 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-4 : Lit)]
  , [(-6 : Lit), (4 : Lit), (5 : Lit)]
  , [(-6 : Lit), (8 : Lit), (9 : Lit)]
  , [(-5 : Lit), (4 : Lit), (6 : Lit)]
  , [(-4 : Lit), (5 : Lit), (6 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (7 : Lit), (8 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def samp27GClosed : List Clause :=
  [ [(-9 : Lit), (3 : Lit)]
  , [(-7 : Lit), (5 : Lit)]
  , [(-5 : Lit), (7 : Lit)]
  , [(-4 : Lit), (1 : Lit)]
  , [(-3 : Lit), (9 : Lit)]
  , [(-1 : Lit), (4 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (-6 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-4 : Lit), (1 : Lit)]
  , [(-9 : Lit), (-4 : Lit), (2 : Lit)]
  , [(-9 : Lit), (-4 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-9 : Lit), (1 : Lit), (3 : Lit)]
  , [(-9 : Lit), (2 : Lit), (3 : Lit)]
  , [(-9 : Lit), (3 : Lit), (4 : Lit)]
  , [(-9 : Lit), (3 : Lit), (6 : Lit)]
  , [(-9 : Lit), (3 : Lit), (8 : Lit)]
  , [(-9 : Lit), (6 : Lit), (8 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (5 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-3 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-8 : Lit), (2 : Lit), (5 : Lit)]
  , [(-8 : Lit), (2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (3 : Lit), (6 : Lit)]
  , [(-8 : Lit), (6 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-4 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-1 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (5 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (1 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (5 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (5 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (5 : Lit)]
  , [(-7 : Lit), (1 : Lit), (5 : Lit)]
  , [(-7 : Lit), (1 : Lit), (6 : Lit)]
  , [(-7 : Lit), (2 : Lit), (5 : Lit)]
  , [(-7 : Lit), (2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (4 : Lit), (5 : Lit)]
  , [(-7 : Lit), (4 : Lit), (6 : Lit)]
  , [(-7 : Lit), (5 : Lit), (6 : Lit)]
  , [(-7 : Lit), (5 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-4 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (1 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-6 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-6 : Lit), (1 : Lit), (5 : Lit)]
  , [(-6 : Lit), (1 : Lit), (7 : Lit)]
  , [(-6 : Lit), (3 : Lit), (8 : Lit)]
  , [(-6 : Lit), (4 : Lit), (5 : Lit)]
  , [(-6 : Lit), (4 : Lit), (7 : Lit)]
  , [(-6 : Lit), (8 : Lit), (9 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (1 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (7 : Lit)]
  , [(-5 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-5 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (1 : Lit), (7 : Lit)]
  , [(-5 : Lit), (2 : Lit), (7 : Lit)]
  , [(-5 : Lit), (2 : Lit), (8 : Lit)]
  , [(-5 : Lit), (4 : Lit), (6 : Lit)]
  , [(-5 : Lit), (4 : Lit), (7 : Lit)]
  , [(-5 : Lit), (6 : Lit), (7 : Lit)]
  , [(-5 : Lit), (7 : Lit), (8 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (1 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (2 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-4 : Lit), (1 : Lit), (2 : Lit)]
  , [(-4 : Lit), (1 : Lit), (3 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (1 : Lit), (6 : Lit)]
  , [(-4 : Lit), (1 : Lit), (7 : Lit)]
  , [(-4 : Lit), (1 : Lit), (9 : Lit)]
  , [(-4 : Lit), (5 : Lit), (6 : Lit)]
  , [(-4 : Lit), (6 : Lit), (7 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-3 : Lit), (1 : Lit), (9 : Lit)]
  , [(-3 : Lit), (2 : Lit), (9 : Lit)]
  , [(-3 : Lit), (4 : Lit), (9 : Lit)]
  , [(-3 : Lit), (6 : Lit), (8 : Lit)]
  , [(-3 : Lit), (6 : Lit), (9 : Lit)]
  , [(-3 : Lit), (8 : Lit), (9 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-2 : Lit), (5 : Lit), (8 : Lit)]
  , [(-2 : Lit), (7 : Lit), (8 : Lit)]
  , [(-1 : Lit), (2 : Lit), (4 : Lit)]
  , [(-1 : Lit), (3 : Lit), (4 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(-1 : Lit), (4 : Lit), (6 : Lit)]
  , [(-1 : Lit), (4 : Lit), (7 : Lit)]
  , [(-1 : Lit), (4 : Lit), (9 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(-1 : Lit), (6 : Lit), (7 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(1 : Lit), (2 : Lit), (9 : Lit)]
  , [(2 : Lit), (3 : Lit), (4 : Lit)]
  , [(2 : Lit), (4 : Lit), (9 : Lit)]
  ]

def samp27GPivots : List Lit := [-11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

def samp27GVres : List Nat := [2, 4, 6, 7, 8, 9]

theorem samp27GVres_eq_samp : samp27GVres = samp27Vres := by native_decide

def samp27GClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem samp27G_closed_bool : samp27GClosedUnder samp27GClosed 3 samp27GPivots = true := by
  native_decide

theorem samp27G_lits_in_pivots :
    (samp27GClosed.all fun C => C.all fun lit => decide (lit ∈ samp27GPivots)) = true := by
  native_decide

theorem samp27G_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ samp27GClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ samp27GPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp samp27G_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem samp27G_mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : samp27GClosedUnder S w pivots = true)
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

def samp27GClosure : WidthClosure 3 where
  axioms := samp27GAxioms
  mem := fun C => C ∈ samp27GClosed
  axiom_mem := by
    intro C hC _
    have h : (samp27GAxioms.all fun A => samp27GClosed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact samp27G_mem_of_closed samp27G_closed_bool hC hD hRes hw (samp27G_pivot hC hRes)

theorem samp27G_no_empty : ¬ samp27GClosure.mem [] := by
  simp [samp27GClosure]
  native_decide

def samp27GProjOK : Bool :=
  samp27GClosed.all fun C =>
    !(supportedOn C samp27Vres) || samp27RClosed.contains C

theorem samp27GProjOK_true : samp27GProjOK = true := by native_decide

theorem samp27G_supported_in_R
    {C : Clause} (hG : C ∈ samp27GClosed) (hsup : supportedOn C samp27Vres = true) :
    C ∈ samp27RClosed := by
  have hall := (List.all_eq_true.mp samp27GProjOK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

def samp27GProjection : ProjectionInclusion 3 where
  gClosure := samp27GClosure
  rClosure := samp27RClosure
  Vres := samp27Vres
  holds := fun _ hG hsup => samp27G_supported_in_R hG hsup

def samp27GEliminationStep : EliminationStep 3 where
  before := samp27GClosure
  after := samp27RClosure
  V_after := samp27Vres
  preserves := fun _ hB hsup => samp27G_supported_in_R hB hsup

theorem samp27G_no_empty_of_projection :
    ¬ samp27GProjection.gClosure.mem [] :=
  no_empty_of_projection samp27GProjection samp27_closure_no_empty

theorem samp27_global_edge_iso_to_residualAxioms (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp27TopologyRename samp27RClosed = true ∧
      residualAxioms e = k4Axioms := by
  refine ⟨?_, residualAxioms_eq_k4 e⟩
  have h := samp27TopologySetEq_true
  simpa [topologySetEq, samp27TopologySetEq] using h

theorem samp27_fresh_g0_projects (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp27TopologyRename samp27RClosed = true ∧
      residualAxioms e = k4Axioms ∧
      ¬ samp27GProjection.gClosure.mem [] :=
  ⟨(samp27_global_edge_iso_to_residualAxioms e).1,
    (samp27_global_edge_iso_to_residualAxioms e).2,
    samp27G_no_empty_of_projection⟩

def samp27GDoc : String :=
  "fresh G₀ Closure₃ for samp27; ProjectionInclusion beyond packs/alts"

end PNPLab.Resolution
