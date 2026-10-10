/-
  Fresh G₀→R for hop-2 sample samp11: C_6 + chords [0, 4],[3, 5].

  Machine fact: Closure₃(G) has size 92 and excludes □; residual
  `samp11RClosed` (16) excludes □; every Closure₃(G) clause supported on
  residual edge vars lies in `samp11RClosed`.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures
import PNPLab.SampleResidualClosures

namespace PNPLab.Resolution

def samp11GAxioms : List Clause :=
  [ [(-5 : Lit), (4 : Lit)]
  , [(-4 : Lit), (1 : Lit)]
  , [(-4 : Lit), (5 : Lit)]
  , [(-1 : Lit), (4 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (-3 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (2 : Lit), (6 : Lit)]
  , [(-8 : Lit), (3 : Lit), (7 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-7 : Lit), (3 : Lit), (8 : Lit)]
  , [(-7 : Lit), (5 : Lit), (6 : Lit)]
  , [(-6 : Lit), (2 : Lit), (8 : Lit)]
  , [(-6 : Lit), (5 : Lit), (7 : Lit)]
  , [(-5 : Lit), (6 : Lit), (7 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (7 : Lit), (8 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (6 : Lit), (8 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def samp11GClosed : List Clause :=
  [ [(-5 : Lit), (1 : Lit)]
  , [(-5 : Lit), (4 : Lit)]
  , [(-4 : Lit), (1 : Lit)]
  , [(-4 : Lit), (5 : Lit)]
  , [(-1 : Lit), (4 : Lit)]
  , [(-1 : Lit), (5 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (-3 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (2 : Lit), (6 : Lit)]
  , [(-8 : Lit), (3 : Lit), (7 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-4 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-1 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (1 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (4 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (1 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (5 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (5 : Lit)]
  , [(-7 : Lit), (1 : Lit), (6 : Lit)]
  , [(-7 : Lit), (3 : Lit), (8 : Lit)]
  , [(-7 : Lit), (4 : Lit), (6 : Lit)]
  , [(-7 : Lit), (5 : Lit), (6 : Lit)]
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
  , [(-5 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-5 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-5 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-5 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (1 : Lit), (2 : Lit)]
  , [(-5 : Lit), (1 : Lit), (3 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (1 : Lit), (7 : Lit)]
  , [(-5 : Lit), (2 : Lit), (4 : Lit)]
  , [(-5 : Lit), (3 : Lit), (4 : Lit)]
  , [(-5 : Lit), (4 : Lit), (6 : Lit)]
  , [(-5 : Lit), (4 : Lit), (7 : Lit)]
  , [(-5 : Lit), (6 : Lit), (7 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (1 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (2 : Lit)]
  , [(-4 : Lit), (-3 : Lit), (5 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (5 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (1 : Lit), (2 : Lit)]
  , [(-4 : Lit), (1 : Lit), (3 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (1 : Lit), (6 : Lit)]
  , [(-4 : Lit), (1 : Lit), (7 : Lit)]
  , [(-4 : Lit), (2 : Lit), (5 : Lit)]
  , [(-4 : Lit), (3 : Lit), (5 : Lit)]
  , [(-4 : Lit), (5 : Lit), (6 : Lit)]
  , [(-4 : Lit), (5 : Lit), (7 : Lit)]
  , [(-4 : Lit), (6 : Lit), (7 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (5 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (5 : Lit)]
  , [(-3 : Lit), (7 : Lit), (8 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (5 : Lit)]
  , [(-2 : Lit), (6 : Lit), (8 : Lit)]
  , [(-1 : Lit), (2 : Lit), (4 : Lit)]
  , [(-1 : Lit), (2 : Lit), (5 : Lit)]
  , [(-1 : Lit), (3 : Lit), (4 : Lit)]
  , [(-1 : Lit), (3 : Lit), (5 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(-1 : Lit), (4 : Lit), (6 : Lit)]
  , [(-1 : Lit), (4 : Lit), (7 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(-1 : Lit), (5 : Lit), (7 : Lit)]
  , [(-1 : Lit), (6 : Lit), (7 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(2 : Lit), (3 : Lit), (4 : Lit)]
  , [(2 : Lit), (3 : Lit), (5 : Lit)]
  ]

def samp11GPivots : List Lit := [-10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

def samp11GVres : List Nat := [2, 3, 4, 6, 7, 8]

theorem samp11GVres_eq_samp : samp11GVres = samp11Vres := by native_decide

def samp11GClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem samp11G_closed_bool : samp11GClosedUnder samp11GClosed 3 samp11GPivots = true := by
  native_decide

theorem samp11G_lits_in_pivots :
    (samp11GClosed.all fun C => C.all fun lit => decide (lit ∈ samp11GPivots)) = true := by
  native_decide

theorem samp11G_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ samp11GClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ samp11GPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp samp11G_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem samp11G_mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : samp11GClosedUnder S w pivots = true)
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

def samp11GClosure : WidthClosure 3 where
  axioms := samp11GAxioms
  mem := fun C => C ∈ samp11GClosed
  axiom_mem := by
    intro C hC _
    have h : (samp11GAxioms.all fun A => samp11GClosed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact samp11G_mem_of_closed samp11G_closed_bool hC hD hRes hw (samp11G_pivot hC hRes)

theorem samp11G_no_empty : ¬ samp11GClosure.mem [] := by
  simp [samp11GClosure]
  native_decide

def samp11GProjOK : Bool :=
  samp11GClosed.all fun C =>
    !(supportedOn C samp11Vres) || samp11RClosed.contains C

theorem samp11GProjOK_true : samp11GProjOK = true := by native_decide

theorem samp11G_supported_in_R
    {C : Clause} (hG : C ∈ samp11GClosed) (hsup : supportedOn C samp11Vres = true) :
    C ∈ samp11RClosed := by
  have hall := (List.all_eq_true.mp samp11GProjOK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

def samp11GProjection : ProjectionInclusion 3 where
  gClosure := samp11GClosure
  rClosure := samp11RClosure
  Vres := samp11Vres
  holds := fun _ hG hsup => samp11G_supported_in_R hG hsup

def samp11GEliminationStep : EliminationStep 3 where
  before := samp11GClosure
  after := samp11RClosure
  V_after := samp11Vres
  preserves := fun _ hB hsup => samp11G_supported_in_R hB hsup

theorem samp11G_no_empty_of_projection :
    ¬ samp11GProjection.gClosure.mem [] :=
  no_empty_of_projection samp11GProjection samp11_closure_no_empty

theorem samp11_global_edge_iso_to_residualAxioms (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp11TopologyRename samp11RClosed = true ∧
      residualAxioms e = k4Axioms := by
  refine ⟨?_, residualAxioms_eq_k4 e⟩
  have h := samp11TopologySetEq_true
  simpa [topologySetEq, samp11TopologySetEq] using h

theorem samp11_fresh_g0_projects (e : Bicyclic.CrossingEndpoints) :
    topologySetEq samp11TopologyRename samp11RClosed = true ∧
      residualAxioms e = k4Axioms ∧
      ¬ samp11GProjection.gClosure.mem [] :=
  ⟨(samp11_global_edge_iso_to_residualAxioms e).1,
    (samp11_global_edge_iso_to_residualAxioms e).2,
    samp11G_no_empty_of_projection⟩

def samp11GDoc : String :=
  "fresh G₀ Closure₃ for samp11; ProjectionInclusion beyond packs/alts"

end PNPLab.Resolution
