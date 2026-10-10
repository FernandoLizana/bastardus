/-
  First non-pack WidthClosure synthesis slice (Category C / G5).

  The six `alt*` residuals already have axiom lists + topology set-eq to
  `k4Closed`. This module packages each as a real `WidthClosure 3` and
  discharges `¬ mem []` — the smallest step beyond pack-only witnesses.
-/

import PNPLab.AltResidualWitnesses
import PNPLab.K4Width3
import PNPLab.ParametricClosure3
import PNPLab.ConcreteClosures
import PNPLab.ResidualAxiomsFromEndpoints

namespace PNPLab.Resolution

/-- Pivot range covering all alt residual literals (|ℓ| ≤ 9). -/
def altSynthPivots : List Lit :=
  [-10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

theorem alt_lits_in_pivots (S : List Clause)
    (h : (S.all fun C => C.all fun lit => decide (lit ∈ altSynthPivots)) = true)
    {C D R : Clause} {p : Lit}
    (hC : C ∈ S) (hRes : resolveOriented C D p = some R) :
    p ∈ altSynthPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp h) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem alt1_lits_ok :
    (alt1RClosed.all fun C => C.all fun lit => decide (lit ∈ altSynthPivots)) = true := by
  native_decide
theorem alt2_lits_ok :
    (alt2RClosed.all fun C => C.all fun lit => decide (lit ∈ altSynthPivots)) = true := by
  native_decide
theorem alt3_lits_ok :
    (alt3RClosed.all fun C => C.all fun lit => decide (lit ∈ altSynthPivots)) = true := by
  native_decide
theorem alt4_lits_ok :
    (alt4RClosed.all fun C => C.all fun lit => decide (lit ∈ altSynthPivots)) = true := by
  native_decide
theorem alt5_lits_ok :
    (alt5RClosed.all fun C => C.all fun lit => decide (lit ∈ altSynthPivots)) = true := by
  native_decide
theorem alt6_lits_ok :
    (alt6RClosed.all fun C => C.all fun lit => decide (lit ∈ altSynthPivots)) = true := by
  native_decide

theorem alt1_closed_bool : k4ClosedUnder alt1RClosed 3 altSynthPivots = true := by
  native_decide
theorem alt2_closed_bool : k4ClosedUnder alt2RClosed 3 altSynthPivots = true := by
  native_decide
theorem alt3_closed_bool : k4ClosedUnder alt3RClosed 3 altSynthPivots = true := by
  native_decide
theorem alt4_closed_bool : k4ClosedUnder alt4RClosed 3 altSynthPivots = true := by
  native_decide
theorem alt5_closed_bool : k4ClosedUnder alt5RClosed 3 altSynthPivots = true := by
  native_decide
theorem alt6_closed_bool : k4ClosedUnder alt6RClosed 3 altSynthPivots = true := by
  native_decide

def alt1RClosure : WidthClosure 3 where
  axioms := alt1RAxioms
  mem := fun C => C ∈ alt1RClosed
  axiom_mem := by
    intro C hC _
    simpa [alt1RClosed] using hC
  closed := by
    intro C D R p hC hD hRes hw
    exact k4_mem_of_closed alt1_closed_bool hC hD hRes hw
      (alt_lits_in_pivots alt1RClosed alt1_lits_ok hC hRes)

def alt2RClosure : WidthClosure 3 where
  axioms := alt2RAxioms
  mem := fun C => C ∈ alt2RClosed
  axiom_mem := by
    intro C hC _
    simpa [alt2RClosed] using hC
  closed := by
    intro C D R p hC hD hRes hw
    exact k4_mem_of_closed alt2_closed_bool hC hD hRes hw
      (alt_lits_in_pivots alt2RClosed alt2_lits_ok hC hRes)

def alt3RClosure : WidthClosure 3 where
  axioms := alt3RAxioms
  mem := fun C => C ∈ alt3RClosed
  axiom_mem := by
    intro C hC _
    simpa [alt3RClosed] using hC
  closed := by
    intro C D R p hC hD hRes hw
    exact k4_mem_of_closed alt3_closed_bool hC hD hRes hw
      (alt_lits_in_pivots alt3RClosed alt3_lits_ok hC hRes)

def alt4RClosure : WidthClosure 3 where
  axioms := alt4RAxioms
  mem := fun C => C ∈ alt4RClosed
  axiom_mem := by
    intro C hC _
    simpa [alt4RClosed] using hC
  closed := by
    intro C D R p hC hD hRes hw
    exact k4_mem_of_closed alt4_closed_bool hC hD hRes hw
      (alt_lits_in_pivots alt4RClosed alt4_lits_ok hC hRes)

def alt5RClosure : WidthClosure 3 where
  axioms := alt5RAxioms
  mem := fun C => C ∈ alt5RClosed
  axiom_mem := by
    intro C hC _
    simpa [alt5RClosed] using hC
  closed := by
    intro C D R p hC hD hRes hw
    exact k4_mem_of_closed alt5_closed_bool hC hD hRes hw
      (alt_lits_in_pivots alt5RClosed alt5_lits_ok hC hRes)

def alt6RClosure : WidthClosure 3 where
  axioms := alt6RAxioms
  mem := fun C => C ∈ alt6RClosed
  axiom_mem := by
    intro C hC _
    simpa [alt6RClosed] using hC
  closed := by
    intro C D R p hC hD hRes hw
    exact k4_mem_of_closed alt6_closed_bool hC hD hRes hw
      (alt_lits_in_pivots alt6RClosed alt6_lits_ok hC hRes)

theorem alt1R_closure_no_empty : ¬ alt1RClosure.mem [] := by
  simp [alt1RClosure, alt1RClosed]
  exact alt1R_no_empty

theorem alt2R_closure_no_empty : ¬ alt2RClosure.mem [] := by
  simp [alt2RClosure, alt2RClosed]
  exact alt2R_no_empty

theorem alt3R_closure_no_empty : ¬ alt3RClosure.mem [] := by
  simp [alt3RClosure, alt3RClosed]
  exact alt3R_no_empty

theorem alt4R_closure_no_empty : ¬ alt4RClosure.mem [] := by
  simp [alt4RClosure, alt4RClosed]
  exact alt4R_no_empty

theorem alt5R_closure_no_empty : ¬ alt5RClosure.mem [] := by
  simp [alt5RClosure, alt5RClosed]
  exact alt5R_no_empty

theorem alt6R_closure_no_empty : ¬ alt6RClosure.mem [] := by
  simp [alt6RClosure, alt6RClosed]
  exact alt6R_no_empty

/-- Topology subset ⇒ □-freedom on packaged WidthClosure (alt1). -/
theorem alt1_no_empty_via_topology :
    ¬ alt1RClosure.mem [] := by
  have h := renamedSubset_no_empty alt1TopologyRename alt1RClosed (by
    have := alt1TopologySetEq_true
    simp [alt1TopologySetEq] at this
    exact this.1)
  simpa [alt1RClosure, alt1RClosed] using h

theorem all_alt_RClosures_no_empty :
    ¬ alt1RClosure.mem [] ∧ ¬ alt2RClosure.mem [] ∧ ¬ alt3RClosure.mem [] ∧
      ¬ alt4RClosure.mem [] ∧ ¬ alt5RClosure.mem [] ∧ ¬ alt6RClosure.mem [] :=
  ⟨alt1R_closure_no_empty, alt2R_closure_no_empty, alt3R_closure_no_empty,
    alt4R_closure_no_empty, alt5R_closure_no_empty, alt6R_closure_no_empty⟩

/-- Beyond-pack residual self-projections (R→R; not instance G₀→R). -/
def alt1SelfProjection : ProjectionInclusion 3 :=
  selfProjection 3 alt1RClosure alt1Vres
def alt2SelfProjection : ProjectionInclusion 3 :=
  selfProjection 3 alt2RClosure alt2Vres
def alt3SelfProjection : ProjectionInclusion 3 :=
  selfProjection 3 alt3RClosure alt3Vres
def alt4SelfProjection : ProjectionInclusion 3 :=
  selfProjection 3 alt4RClosure alt4Vres
def alt5SelfProjection : ProjectionInclusion 3 :=
  selfProjection 3 alt5RClosure alt5Vres
def alt6SelfProjection : ProjectionInclusion 3 :=
  selfProjection 3 alt6RClosure alt6Vres

theorem all_alt_self_projections_no_empty :
    ¬ alt1SelfProjection.gClosure.mem [] ∧
      ¬ alt2SelfProjection.gClosure.mem [] ∧
      ¬ alt3SelfProjection.gClosure.mem [] ∧
      ¬ alt4SelfProjection.gClosure.mem [] ∧
      ¬ alt5SelfProjection.gClosure.mem [] ∧
      ¬ alt6SelfProjection.gClosure.mem [] :=
  ⟨no_empty_self_projection alt1RClosure alt1Vres alt1R_closure_no_empty,
    no_empty_self_projection alt2RClosure alt2Vres alt2R_closure_no_empty,
    no_empty_self_projection alt3RClosure alt3Vres alt3R_closure_no_empty,
    no_empty_self_projection alt4RClosure alt4Vres alt4R_closure_no_empty,
    no_empty_self_projection alt5RClosure alt5Vres alt5R_closure_no_empty,
    no_empty_self_projection alt6RClosure alt6Vres alt6R_closure_no_empty⟩

/-- Global-edge alt1 residual ≅ template `residualAxioms` (topology set-eq). -/
theorem alt1_global_edge_iso_to_residualAxioms (e : Bicyclic.CrossingEndpoints) :
    topologySetEq alt1TopologyRename alt1RClosed = true ∧
      residualAxioms e = k4Axioms := by
  refine ⟨?_, residualAxioms_eq_k4 e⟩
  have h := alt1TopologySetEq_true
  simpa [topologySetEq, alt1TopologySetEq] using h

theorem alt2_global_edge_iso_to_residualAxioms (e : Bicyclic.CrossingEndpoints) :
    topologySetEq alt2TopologyRename alt2RClosed = true ∧
      residualAxioms e = k4Axioms := by
  refine ⟨?_, residualAxioms_eq_k4 e⟩
  have h := alt2TopologySetEq_true
  simpa [topologySetEq, alt2TopologySetEq] using h

theorem alt3_global_edge_iso_to_residualAxioms (e : Bicyclic.CrossingEndpoints) :
    topologySetEq alt3TopologyRename alt3RClosed = true ∧
      residualAxioms e = k4Axioms := by
  refine ⟨?_, residualAxioms_eq_k4 e⟩
  have h := alt3TopologySetEq_true
  simpa [topologySetEq, alt3TopologySetEq] using h

theorem alt4_global_edge_iso_to_residualAxioms (e : Bicyclic.CrossingEndpoints) :
    topologySetEq alt4TopologyRename alt4RClosed = true ∧
      residualAxioms e = k4Axioms := by
  refine ⟨?_, residualAxioms_eq_k4 e⟩
  have h := alt4TopologySetEq_true
  simpa [topologySetEq, alt4TopologySetEq] using h

theorem alt5_global_edge_iso_to_residualAxioms (e : Bicyclic.CrossingEndpoints) :
    topologySetEq alt5TopologyRename alt5RClosed = true ∧
      residualAxioms e = k4Axioms := by
  refine ⟨?_, residualAxioms_eq_k4 e⟩
  have h := alt5TopologySetEq_true
  simpa [topologySetEq, alt5TopologySetEq] using h

theorem alt6_global_edge_iso_to_residualAxioms (e : Bicyclic.CrossingEndpoints) :
    topologySetEq alt6TopologyRename alt6RClosed = true ∧
      residualAxioms e = k4Axioms := by
  refine ⟨?_, residualAxioms_eq_k4 e⟩
  have h := alt6TopologySetEq_true
  simpa [topologySetEq, alt6TopologySetEq] using h

/-- All six alt residuals ≅ template `residualAxioms`. -/
theorem all_alt_iso_to_residualAxioms (e : Bicyclic.CrossingEndpoints) :
    (alt1TopologySetEq = true ∧ alt2TopologySetEq = true ∧ alt3TopologySetEq = true ∧
      alt4TopologySetEq = true ∧ alt5TopologySetEq = true ∧ alt6TopologySetEq = true) ∧
      residualAxioms e = k4Axioms :=
  ⟨all_alt_topology_set_eq, residualAxioms_eq_k4 e⟩

/-- Packaging complete: 6 alt residuals as `WidthClosure 3`. -/
def altResidualClosuresCount : Nat := 6

theorem altResidualClosuresCount_eq : altResidualClosuresCount = 6 := rfl

def altResidualClosuresDoc : String :=
  "alt1..alt6 WidthClosure 3 + self-projections; all ≅ residualAxioms; " ++
  "alt1 fresh G₀→R in Alt1FoldProjection"

end PNPLab.Resolution
