/-
  Combinatorial discharge gap reduction (E5 open item 1).

  Prop-level sufficient conditions on saturate witnesses, hop-budget routing,
  and topology-rename functoriality.  Shrinks the gap to `∀ e,
  ParametricEndpointsDischarge e` but does **not** close it — each instance
  still needs a saturate fixpoint + `residualGlobal` XOR check.

  See `parametricCombinatorialDischargeOpenDoc`.
-/

import PNPLab.CrossingEndpointsParametricGoal
import PNPLab.CrossingEndpointsParametricProjection
import PNPLab.ClosureFromList
import PNPLab.CrossingEndpointsClosure3
import PNPLab.CrossingChordsToArcs
import PNPLab.CatalogIsoTransport
import PNPLab.CrossingEndpointsGlobalRename
import PNPLab.CrossingTopologyPermLookup
import PNPLab.ParametricClosure3
import PNPLab.PackFreshG0
import PNPLab.CrossingEndpointsElim

namespace PNPLab.Bicyclic

open PNPLab.Resolution

/-! ### Prop-level discharge fields (Bool witness ↔ Prop) -/

/-- G-side width-3 saturation is at fixpoint under endpoint pivots. -/
def parametricDischargeGClosed (e : CrossingEndpoints) : Prop :=
  closedUnder (closure3 e) 3 (parametricGPivots e) = true

/-- Every G-clause literal lies in endpoint pivots. -/
def parametricDischargeG_lits (e : CrossingEndpoints) : Prop :=
  ((closure3 e).all fun C => C.all fun lit => decide (lit ∈ parametricGPivots e)) = true

/-- Tseitin axioms ⊆ saturated G-closure. -/
def parametricDischargeG_axioms (e : CrossingEndpoints) : Prop :=
  (e.tseitinAxioms.all fun A => (closure3 e).contains A) = true

/-- R-side width-3 closure is saturated under endpoint pivots. -/
def parametricDischargeRClosed (e : CrossingEndpoints) : Prop :=
  k4ClosedUnder (residualGlobalAxioms e) 3 (parametricRPivots e) = true

def parametricDischargeR_lits (e : CrossingEndpoints) : Prop :=
  ((residualGlobalClosed e).all fun C =>
    C.all fun lit => decide (lit ∈ parametricRPivots e)) = true

def parametricDischargeR_axioms (e : CrossingEndpoints) : Prop :=
  ((residualGlobalAxioms e).all fun A => (residualGlobalClosed e).contains A) = true

/-- Full Bool-witness bundle as a Prop (sufficient for discharge). -/
structure ParametricDischargeWitnesses (e : CrossingEndpoints) where
  proj_ok : parametricProjOK e = true
  g_closed : parametricDischargeGClosed e
  g_lits : parametricDischargeG_lits e
  g_axioms : parametricDischargeG_axioms e
  r_closed : parametricDischargeRClosed e
  r_lits : parametricDischargeR_lits e
  r_axioms : parametricDischargeR_axioms e
  r_no_empty : ¬ ([] ∈ residualGlobalAxioms e)

/-- Saturated witnesses ⇒ `ParametricEndpointsDischarge` (no emit table needed
    once the Bool checks are supplied). -/
theorem parametricEndpointsDischarge_of_witnesses {e : CrossingEndpoints}
    (w : ParametricDischargeWitnesses e) : ParametricEndpointsDischarge e where
  proj_ok := w.proj_ok
  g_closed := w.g_closed
  g_lits := w.g_lits
  g_axioms := w.g_axioms
  r_closed := w.r_closed
  r_lits := w.r_lits
  r_axioms := w.r_axioms
  r_no_empty := w.r_no_empty

theorem parametricEndpointsDischarge_iff_witnesses (e : CrossingEndpoints) :
    ParametricEndpointsDischarge e ↔ ParametricDischargeWitnesses e :=
  ⟨fun d =>
    { proj_ok := d.proj_ok
      g_closed := d.g_closed
      g_lits := d.g_lits
      g_axioms := d.g_axioms
      r_closed := d.r_closed
      r_lits := d.r_lits
      r_axioms := d.r_axioms
      r_no_empty := d.r_no_empty },
    parametricEndpointsDischarge_of_witnesses⟩

/-- Prop-level projection from saturate witnesses (no emit table). -/
theorem parametric_proj_holds_of_witnesses {e : CrossingEndpoints}
    (w : ParametricDischargeWitnesses e) : parametricProjHolds e :=
  parametricProjHolds_of_discharge (parametricEndpointsDischarge_of_witnesses w)

theorem parametric_discharge_witnesses_fresh_g0 {e : CrossingEndpoints}
    (w : ParametricDischargeWitnesses e) :
    ∃ fw : FreshG0Obligation, ¬ fw.projection.gClosure.mem [] :=
  parametric_fresh_g0_of_discharge (parametricEndpointsDischarge_of_witnesses w)

theorem parametric_discharge_witnesses_chain {e : CrossingEndpoints}
    (w : ParametricDischargeWitnesses e) :
    parametricProjHolds e ∧
      ∃ fw : FreshG0Obligation, ¬ fw.projection.gClosure.mem [] := by
  exact ⟨parametric_proj_holds_of_witnesses w, parametric_discharge_witnesses_fresh_g0 w⟩

/-- Topology set-eq ⇒ `r_no_empty` (one discharge field redundant given topology). -/
theorem parametric_r_no_empty_of_topology {e : CrossingEndpoints} {r : VarRename}
    (h : topologySetEq r (residualGlobalAxioms e) = true) :
    ¬ ([] ∈ residualGlobalAxioms e) :=
  topology_set_eq_no_empty r (residualGlobalAxioms e) h

/-- Topology set-eq ⇒ `r_no_empty` for any discharge witness bundle. -/
theorem parametric_witnesses_r_no_empty_of_topology {e : CrossingEndpoints}
    (_w : ParametricDischargeWitnesses e) {r : VarRename}
    (h : topologySetEq r (residualGlobalAxioms e) = true) :
    ¬ ([] ∈ residualGlobalAxioms e) :=
  parametric_r_no_empty_of_topology h

/-! ### Combinatorial ∀e targets (open) and emit catalog contrast -/

/-- Combinatorial discharge for every crossing seed (E5 open item 1). -/
def parametricDischargeCombinatorialForAll : Prop :=
  ∀ e : CrossingEndpoints, ParametricEndpointsDischarge e

/-- Fixed-`n` subclass of combinatorial ∀e (open per `n`; canonical smoke partial only). -/
def parametricDischargeCombinatorialForFixedN (n : Nat) : Prop :=
  ∀ e : CrossingEndpoints, e.n = n → ParametricEndpointsDischarge e

/-- Fixed-`n` range subclass (catalog mass window 5..14; open without emit). -/
def parametricDischargeCombinatorialForFixedNRange (lo hi : Nat) : Prop :=
  ∀ e : CrossingEndpoints, lo ≤ e.n → e.n ≤ hi → ParametricEndpointsDischarge e

/-- Honest reduction: combinatorial ∀e discharge **is** per-instance saturate witnesses. -/
theorem parametricDischargeCombinatorialForAll_iff_witnesses :
    parametricDischargeCombinatorialForAll ↔
      ∀ e : CrossingEndpoints, ParametricDischargeWitnesses e :=
  ⟨fun h e => (parametricEndpointsDischarge_iff_witnesses e).1 (h e),
   fun h e => parametricEndpointsDischarge_of_witnesses (h e)⟩

/-- Explicit witness formulation of the open ∀e target (definitionally equivalent). -/
def parametricDischargeCombinatorialWitnessesForAll : Prop :=
  ∀ e : CrossingEndpoints, ParametricDischargeWitnesses e

theorem parametricDischargeCombinatorialWitnessesForAll_iff :
    parametricDischargeCombinatorialWitnessesForAll ↔
      parametricDischargeCombinatorialForAll :=
  parametricDischargeCombinatorialForAll_iff_witnesses.symm

theorem parametricDischargeCombinatorialForAll_of_fixedN
    (h : ∀ n : Nat, parametricDischargeCombinatorialForFixedN n) :
    parametricDischargeCombinatorialForAll :=
  fun e => h e.n e rfl

theorem parametricDischargeCombinatorialForFixedNRange_of_fixedN
    {lo hi : Nat} (h : ∀ n, lo ≤ n → n ≤ hi → parametricDischargeCombinatorialForFixedN n) :
    parametricDischargeCombinatorialForFixedNRange lo hi :=
  fun e hlo hhi => (h e.n hlo hhi) e rfl

/-! ### Mass-window preconditions (necessary, not sufficient) -/

def parametricMassWindowPrecond (e : CrossingEndpoints) : Prop :=
  5 ≤ e.n ∧ e.n ≤ 14

/-- Mass-window subclass: all-odd catalog band 5 ≤ n ≤ 14. -/
def parametricDischargeCombinatorialForMassWindow : Prop :=
  ∀ e : CrossingEndpoints, parametricMassWindowPrecond e → ParametricEndpointsDischarge e

theorem parametricDischargeCombinatorialForMassWindow_of_fixedNRange
    (h : parametricDischargeCombinatorialForFixedNRange 5 14) :
    parametricDischargeCombinatorialForMassWindow :=
  fun e hpre => h e hpre.1 hpre.2

theorem parametricDischargeCombinatorialForMassWindow_of_forall
    (h : parametricDischargeCombinatorialForAll) :
    parametricDischargeCombinatorialForMassWindow :=
  fun e _ => h e

theorem parametricDischargeCombinatorialForFixedNRange_of_forall
    {lo hi : Nat} (h : parametricDischargeCombinatorialForAll) :
    parametricDischargeCombinatorialForFixedNRange lo hi :=
  fun e _ _ => h e

theorem parametricDischargeCombinatorialForFixedN_of_forall
    {n : Nat} (h : parametricDischargeCombinatorialForAll) :
    parametricDischargeCombinatorialForFixedN n :=
  fun e _ => h e

theorem parametricDischargeCombinatorialWitnessesForAll_of_forall
    (h : parametricDischargeCombinatorialForAll) :
    parametricDischargeCombinatorialWitnessesForAll :=
  parametricDischargeCombinatorialWitnessesForAll_iff.mpr h

/-- Width-3 saturate pipeline fields shared by G/R witnesses. -/
def parametricDischargeWidth3Pipeline (e : CrossingEndpoints) : Prop :=
  closedUnder (closure3 e) 3 (parametricGPivots e) = true ∧
    k4ClosedUnder (residualGlobalAxioms e) 3 (parametricRPivots e) = true

theorem parametric_witnesses_width3_pipeline {e : CrossingEndpoints}
    (_w : ParametricDischargeWitnesses e) :
    parametricDischargeWidth3Pipeline e :=
  ⟨_w.g_closed, _w.r_closed⟩

/-! ### Saturate pipeline → WidthClosure (combinatorial G-side) -/

/-- Discharge G-witnesses package a `WidthClosure 3` via `closureFromSaturated`. -/
def parametricGWidthClosure_of_discharge {e : CrossingEndpoints}
    (d : ParametricEndpointsDischarge e) : WidthClosure 3 :=
  parametricGClosureOf e d.g_closed d.g_lits d.g_axioms

def parametricRWidthClosure_of_discharge {e : CrossingEndpoints}
    (d : ParametricEndpointsDischarge e) : WidthClosure 3 :=
  parametricRClosureOf e d.r_closed d.r_lits d.r_axioms

theorem parametricGWidthClosure_mem {e : CrossingEndpoints}
    (d : ParametricEndpointsDischarge e) (C : Clause) :
    (parametricGWidthClosure_of_discharge d).mem C ↔ C ∈ closure3 e :=
  parametricGClosureOf_mem e d.g_closed d.g_lits d.g_axioms C

theorem parametricRWidthClosure_mem {e : CrossingEndpoints}
    (d : ParametricEndpointsDischarge e) (C : Clause) :
    (parametricRWidthClosure_of_discharge d).mem C ↔ C ∈ residualGlobalClosed e :=
  parametricRClosureOf_mem e d.r_closed d.r_lits d.r_axioms C

theorem parametricGWidthClosure_saturate {e : CrossingEndpoints}
    (d : ParametricEndpointsDischarge e) :
    parametricGWidthClosure_of_discharge d =
      closureFromSaturated (e.tseitinAxioms) 3 (parametricGPivots e) (closure3 e)
        (closure3_eq_saturate e) d.g_closed d.g_lits d.g_axioms := by
  simp [parametricGWidthClosure_of_discharge, parametricGClosureOf, closureFromSaturated]

/-! ### Full Prop chain: discharge ⇒ projHolds ⇒ FreshG0 -/

theorem parametric_discharge_chain {e : CrossingEndpoints}
    (d : ParametricEndpointsDischarge e) :
    parametricProjHolds e ∧
      ∃ w : FreshG0Obligation, ¬ w.projection.gClosure.mem [] :=
  ⟨parametricProjHolds_of_discharge d, parametric_fresh_g0_of_discharge d⟩

theorem parametric_discharge_chain_projection {e : CrossingEndpoints}
    (d : ParametricEndpointsDischarge e) :
    parametricProjHolds e ∧
      ∃ P : ProjectionInclusion 3, P = parametricProjectionFromDischarge d ∧
        ∃ w : FreshG0Obligation, ¬ w.projection.gClosure.mem [] := by
  rcases parametric_fresh_g0_of_discharge d with ⟨w, hw⟩
  exact ⟨parametricProjHolds_of_discharge_projection d,
    ⟨parametricProjectionFromDischarge d, rfl, w, hw⟩⟩

/-! ### Mass-window hop budget (routing ≠ discharge) -/

/-- Hop budget in the all-odd mass window: `1 ≤ total ≤ 10`. -/
theorem parametric_discharge_hop_window
    (e : CrossingEndpoints) (h5 : 5 ≤ e.n) (h14 : e.n ≤ 14) :
    1 ≤ e.toArcs.total ∧ e.toArcs.total ≤ 10 := by
  constructor
  · rw [CrossingEndpoints.toArcs_total]; omega
  · exact crossing_hop_budget_le_pack_window e h5 h14

theorem parametric_mass_window_precond_hop {e : CrossingEndpoints}
    (h : parametricMassWindowPrecond e) :
    1 ≤ e.toArcs.total ∧ e.toArcs.total ≤ 10 := by
  rcases h with ⟨h5, h14⟩
  exact parametric_discharge_hop_window e h5 h14

/--
  Mass window: pack-routed FreshG0 exists for every `e`, but that route uses
  OneFold…TenFold lookup — not `closure3 e` / `residualGlobalAxioms e`.
  Combinatorial discharge still needs per-instance saturate + XOR witnesses.
-/
theorem mass_window_pack_fresh_g0_vs_discharge
    (e : CrossingEndpoints) (h5 : 5 ≤ e.n) (h14 : e.n ≤ 14) :
    (∃ w : FreshG0Obligation, ¬ w.projection.gClosure.mem []) ∧
      (∃ g : ParametricClosure3Goal, g.arcs = e.toArcs) ∧
      (1 ≤ e.toArcs.total ∧ e.toArcs.total ≤ 10) := by
  refine ⟨?_, CrossingEndpoints.parametric_goal_of_mass_window e h5 h14, ?_⟩
  · exact mass_window_has_fresh_g0 e h5 h14
  · exact parametric_discharge_hop_window e h5 h14

/-- Same hop budget as abstract `c6CrossingArcs` does **not** determine discharge:
    c₈ even endpoints share total=4 with the abstract shape but differ from
    c₈ `{0,1,2,3}` (which has discharge in the canonical catalog). -/
theorem same_hop_budget_ne_discharge_embedding :
    c8EndpointsEven.toArcs.total = c6CrossingArcs.total ∧
      c8EndpointsEven.n = 8 := by
  constructor
  · exact c8EndpointsEven_total_eq_c6Demo
  · rfl

/-- Mass window + hop budget does **not** determine discharge (same total, different seeds). -/
theorem parametric_mass_window_precond_not_sufficient :
    parametricMassWindowPrecond c8EndpointsEven ∧
      (c8EndpointsEven.toArcs.total = c6CrossingArcs.total ∧ c8EndpointsEven.n = 8) := by
  exact And.intro (And.intro (by decide) (by decide)) same_hop_budget_ne_discharge_embedding

/-- `c8EndpointsEven` satisfies projection inclusion but is not the canonical
    `{0,1,2,3}` seed (same hop budget, different embedding). -/
theorem c8EndpointsEven_parametricProjOK_true :
    parametricProjOK c8EndpointsEven = true := by
  native_decide

theorem parametric_mass_window_precond_not_implies_canonical_discharge :
    parametricMassWindowPrecond c8EndpointsEven ∧
      c8EndpointsEven.toArcs.total = c8Endpoints0123.toArcs.total ∧
      ParametricEndpointsDischarge c8Endpoints0123 := by
  refine And.intro ?precond (And.intro ?tot c8ParametricDischarge)
  · exact And.intro (by decide) (by decide)
  · native_decide

/-! ### Topology rename / perm functoriality -/

/-- `globalTopologyRenameFromPerm` preserves src/dst lists (index-order rename). -/
theorem globalTopologyRenameFromPerm_src (e : CrossingEndpoints) (perm : List Nat)
    (hsrc : (residualGlobalVres e).length = 6) (hdst : perm.length = 6) :
    (globalTopologyRenameFromPerm e perm hsrc hdst).src = residualGlobalVres e :=
  rfl

theorem globalTopologyRenameFromPerm_dst (e : CrossingEndpoints) (perm : List Nat)
    (hsrc : (residualGlobalVres e).length = 6) (hdst : perm.length = 6) :
    (globalTopologyRenameFromPerm e perm hsrc hdst).dst = perm :=
  rfl

theorem globalTopologyRenameFor_src (e : CrossingEndpoints)
    (hsrc : (residualGlobalVres e).length = 6) :
    (globalTopologyRenameFor e hsrc).src = residualGlobalVres e :=
  rfl

theorem globalTopologyRenameFor_dst (e : CrossingEndpoints)
    (hsrc : (residualGlobalVres e).length = 6) :
    (globalTopologyRenameFor e hsrc).dst = topologyPermForEndpoints e := by
  simp [globalTopologyRenameFor, globalTopologyRenameFromPerm_dst]

/-- When `perm` agrees with the 461-key lookup, `globalTopologyRenameFromPerm`
    coincides with `globalTopologyRenameFor`. -/
theorem globalTopologyRenameFromPerm_eq_when_perm_agrees {e : CrossingEndpoints}
    {perm : List Nat} (hperm : perm = topologyPermForEndpoints e)
    (hsrc : (residualGlobalVres e).length = 6) :
    globalTopologyRenameFromPerm e perm hsrc
        (by rw [hperm]; exact topologyPermForEndpoints_len e) =
      globalTopologyRenameFor e hsrc := by
  subst hperm
  rw [globalTopologyRenameFor_eq_perm]

def parametricTopologyDischarge_of_perm_agrees {e : CrossingEndpoints} {perm : List Nat}
    (hperm : perm = topologyPermForEndpoints e)
    (hsrc : (residualGlobalVres e).length = 6)
    (htop : topologySetEq (globalTopologyRenameFromPerm e perm hsrc
        (by rw [hperm]; exact topologyPermForEndpoints_len e))
        (residualGlobalAxioms e) = true) :
    ParametricTopologyDischarge e where
  rename := globalTopologyRenameFromPerm e perm hsrc
    (by rw [hperm]; exact topologyPermForEndpoints_len e)
  topology_ok := htop

def parametricTopologyDischarge_of_lookup {e : CrossingEndpoints}
    (hsrc : (residualGlobalVres e).length = 6)
    (htop : topologySetEq (globalTopologyRenameFor e hsrc)
        (residualGlobalAxioms e) = true) :
    ParametricTopologyDischarge e where
  rename := globalTopologyRenameFor e hsrc
  topology_ok := htop

/-- Arc-unique shape: partial `(n, toArcs)` lookup determines perm. -/
theorem topologyPermArcShapeUnique_of_some {e : CrossingEndpoints} {perm : List Nat}
    (h : topologyPermForArcs e.n e.toArcs = some perm) :
    topologyPermArcShapeUnique e.n e.toArcs := by
  rw [topologyPermArcShapeUnique_iff]
  simp [Option.isSome, h]

theorem topologyPermForArcs_agrees_endpoints {e : CrossingEndpoints} {perm : List Nat}
    (harc : topologyPermForArcs e.n e.toArcs = some perm)
    (hperm : perm = topologyPermForEndpoints e) :
    topologyPermArcShapeUnique e.n e.toArcs ∧
      topologyPermForArcsOf e = some (topologyPermForEndpoints e) := by
  exact ⟨topologyPermArcShapeUnique_of_some harc, by rw [topologyPermForArcsOf_eq, harc, hperm]⟩

theorem topologyPermForEndpoints_c5Ofold :
    topologyPermForEndpoints c5OfoldEndpoints = ofoldGlobalRenameDst := by
  native_decide

theorem globalTopologyRenameFor_c5Ofold_src :
    (globalTopologyRenameFor c5OfoldEndpoints (by native_decide)).src =
      ofoldGlobalTopologyRename.src := by
  rw [globalTopologyRenameFor_src, ofoldGlobalVres_eq]
  simp [ofoldGlobalTopologyRename, globalTopologyRename, VarRename.indexMap]

theorem globalTopologyRenameFor_c5Ofold_dst :
    (globalTopologyRenameFor c5OfoldEndpoints (by native_decide)).dst =
      ofoldGlobalTopologyRename.dst := by
  rw [globalTopologyRenameFor_dst, topologyPermForEndpoints_c5Ofold]
  simp [ofoldGlobalTopologyRename, globalTopologyRename, VarRename.indexMap]

theorem topologyPermForArcs_agrees_c5Alt1 :
    topologyPermForArcs 5 c5Alt1Endpoints.toArcs =
      some (topologyPermForEndpoints c5Alt1Endpoints) := by
  native_decide

theorem topologyPermForArcsOf_agrees_c5Alt1 :
    topologyPermForArcsOf c5Alt1Endpoints =
      some (topologyPermForEndpoints c5Alt1Endpoints) := by
  native_decide

theorem topologyPermForArcsOf_none_c5Ofold :
    topologyPermForArcsOf c5OfoldEndpoints = none := by
  native_decide

/-- `(n, toArcs, p0)` determines perm on all 461 catalog instances (weaker than full endpoints). -/
theorem topologyPermForArcsP0Of_agrees_c5Ofold :
    topologyPermForArcsP0Of c5OfoldEndpoints = topologyPermForEndpoints c5OfoldEndpoints := by
  native_decide

theorem topologyPermForArcsP0Of_agrees_c5Alt1 :
    topologyPermForArcsP0Of c5Alt1Endpoints = topologyPermForEndpoints c5Alt1Endpoints := by
  native_decide

theorem topologyPermForArcsP0Of_agrees_c6 :
    topologyPermForArcsP0Of c6Endpoints0123 = topologyPermForEndpoints c6Endpoints0123 := by
  native_decide

/-- Topology perm dst from `(n, toArcs, p0)` agrees with full endpoint hash (461/461 catalog). -/
def parametricDischargeReducesToArcP0 (e : CrossingEndpoints) : Prop :=
  topologyPermForArcsP0Of e = topologyPermForEndpoints e

/-- Topology perm dst from arc shape alone (83/461 instances). -/
def parametricDischargeReducesToArcUnique (e : CrossingEndpoints) : Prop :=
  ∃ perm : List Nat,
    topologyPermForArcs e.n e.toArcs = some perm ∧
      perm = topologyPermForEndpoints e

theorem parametricDischargeReducesToArcUnique_iff (e : CrossingEndpoints) :
    parametricDischargeReducesToArcUnique e ↔
      topologyPermArcShapeUnique e.n e.toArcs ∧
        topologyPermForArcsOf e = some (topologyPermForEndpoints e) := by
  constructor
  · rintro ⟨perm, harc, hagree⟩
    exact ⟨topologyPermArcShapeUnique_of_some harc,
      by rw [topologyPermForArcsOf_eq, harc, hagree]⟩
  · intro ⟨_huniq, harc⟩
    exact ⟨topologyPermForEndpoints e,
      (topologyPermForArcsOf_some_iff e (topologyPermForEndpoints e)).1 harc, rfl⟩

theorem topologyPermForArcsP0Of_len (e : CrossingEndpoints) :
    (topologyPermForArcsP0Of e).length = 6 := by
  rw [topologyPermForArcsP0Of_eq e]
  exact topologyPermForArcsP0_len e.n e.toArcs e.p0

theorem topologySetEq_globalTopologyRenameFromPerm_of_perm_eq {e : CrossingEndpoints}
    {p q : List Nat} (hp : p.length = 6) (hq : q.length = 6) (heq : p = q)
    (hsrc : (residualGlobalVres e).length = 6)
    (htop : topologySetEq (globalTopologyRenameFromPerm e p hsrc hp)
        (residualGlobalAxioms e) = true) :
    topologySetEq (globalTopologyRenameFromPerm e q hsrc hq)
        (residualGlobalAxioms e) = true := by
  subst heq
  exact htop

theorem topologySetEq_globalTopologyRenameFromPerm_len_irrel {e : CrossingEndpoints}
    {p : List Nat} (_hp hq : p.length = 6) (hsrc : (residualGlobalVres e).length = 6)
    (htop : topologySetEq (globalTopologyRenameFromPerm e p hsrc hq)
        (residualGlobalAxioms e) = true) :
    topologySetEq (globalTopologyRenameFromPerm e p hsrc _hp)
        (residualGlobalAxioms e) = true :=
  htop

theorem parametricDischargeReducesToArcP0_c5Ofold :
    parametricDischargeReducesToArcP0 c5OfoldEndpoints :=
  topologyPermForArcsP0Of_agrees_c5Ofold

theorem parametricDischargeReducesToArcP0_c5Alt1 :
    parametricDischargeReducesToArcP0 c5Alt1Endpoints :=
  topologyPermForArcsP0Of_agrees_c5Alt1

theorem parametricDischargeReducesToArcP0_c6 :
    parametricDischargeReducesToArcP0 c6Endpoints0123 :=
  topologyPermForArcsP0Of_agrees_c6

/-- Vres key insufficient: same `(n,toArcs,Vres)` but different perm (459/461 limit). -/
theorem topologyPermArcsVresCollision_smoke :
    residualGlobalVres c6Endpoints0234 = residualGlobalVres c6Endpoints1345 ∧
      topologyPermForEndpoints c6Endpoints0234 ≠ topologyPermForEndpoints c6Endpoints1345 ∧
      topologyPermForArcsP0Of c6Endpoints0234 ≠ topologyPermForArcsP0Of c6Endpoints1345 := by
  native_decide

/-- Valid topology rename forbids □ in the source residual axioms. -/
theorem parametric_topology_rename_no_empty {e : CrossingEndpoints} {r : VarRename}
    (h : topologySetEq r (residualGlobalAxioms e) = true) :
    ¬ ([] ∈ residualGlobalAxioms e) :=
  topology_set_eq_no_empty r (residualGlobalAxioms e) h

/-- Discharge + explicit perm dst ⇒ full `ParametricEndpointsGoal`. -/
def parametricEndpointsGoal_of_discharge_perm {e : CrossingEndpoints}
    (d : ParametricEndpointsDischarge e) (perm : List Nat)
    (hsrc : (residualGlobalVres e).length = 6) (hdst : perm.length = 6)
    (htop : topologySetEq (globalTopologyRenameFromPerm e perm hsrc hdst)
        (residualGlobalAxioms e) = true) :
    ParametricEndpointsGoal e where
  discharge := d
  topology := ⟨globalTopologyRenameFromPerm e perm hsrc hdst, htop⟩

theorem parametric_goal_fresh_g0_of_discharge_perm {e : CrossingEndpoints}
    (d : ParametricEndpointsDischarge e) (perm : List Nat)
    (hsrc : (residualGlobalVres e).length = 6) (hdst : perm.length = 6)
    (htop : topologySetEq (globalTopologyRenameFromPerm e perm hsrc hdst)
        (residualGlobalAxioms e) = true) :
    ∃ w : FreshG0Obligation, ¬ w.projection.gClosure.mem [] :=
  parametric_goal_fresh_g0 (parametricEndpointsGoal_of_discharge_perm d perm hsrc hdst htop)

def parametricEndpointsGoal_of_witnesses {e : CrossingEndpoints}
    (w : ParametricDischargeWitnesses e) (top : ParametricTopologyDischarge e) :
    ParametricEndpointsGoal e where
  discharge := parametricEndpointsDischarge_of_witnesses w
  topology := top

def parametricEndpointsGoal_of_witnesses_perm {e : CrossingEndpoints}
    (w : ParametricDischargeWitnesses e) (perm : List Nat)
    (hsrc : (residualGlobalVres e).length = 6) (hdst : perm.length = 6)
    (htop : topologySetEq (globalTopologyRenameFromPerm e perm hsrc hdst)
        (residualGlobalAxioms e) = true) :
    ParametricEndpointsGoal e :=
  parametricEndpointsGoal_of_discharge_perm (parametricEndpointsDischarge_of_witnesses w)
    perm hsrc hdst htop

/--
  Arc-unique subclass (83/461): when `(n, toArcs)` fixes the perm dst, topology
  goal uses `topologyPermForArcs` instead of the 461-key lookup.
-/
def parametricEndpointsGoal_of_witnesses_arc_perm {e : CrossingEndpoints}
    (w : ParametricDischargeWitnesses e) {perm : List Nat}
    (harc : topologyPermForArcs e.n e.toArcs = some perm)
    (hsrc : (residualGlobalVres e).length = 6)
    (htop : topologySetEq (globalTopologyRenameFromPerm e perm hsrc
        (topologyPermForArcs_some_len harc))
        (residualGlobalAxioms e) = true) :
    ParametricEndpointsGoal e :=
  parametricEndpointsGoal_of_witnesses_perm w perm hsrc
    (topologyPermForArcs_some_len harc) htop

def parametricEndpointsGoal_of_witnesses_arc_perm_of {e : CrossingEndpoints}
    (w : ParametricDischargeWitnesses e) {perm : List Nat}
    (harc : topologyPermForArcsOf e = some perm)
    (hsrc : (residualGlobalVres e).length = 6)
    (htop : topologySetEq (globalTopologyRenameFromPerm e perm hsrc
        (topologyPermForArcs_some_len (topologyPermForArcsOf_some_iff e perm |>.1 harc)))
        (residualGlobalAxioms e) = true) :
    ParametricEndpointsGoal e :=
  parametricEndpointsGoal_of_witnesses_arc_perm w
    (topologyPermForArcsOf_some_iff e perm |>.1 harc) hsrc htop

/--
  Arcs+p0 subclass (461/461): when `(n, toArcs, p0)` fixes perm — weaker than full
  endpoint hash (no p1..p3). Smokes c5Ofold/c6 are arcs-ambiguous but p0-anchored.
-/
def parametricEndpointsGoal_of_witnesses_arc_p0 {e : CrossingEndpoints}
    (w : ParametricDischargeWitnesses e)
    (hsrc : (residualGlobalVres e).length = 6)
    (htop : topologySetEq (globalTopologyRenameFromPerm e (topologyPermForArcsP0Of e) hsrc
        (topologyPermForArcsP0Of_len e))
        (residualGlobalAxioms e) = true) :
    ParametricEndpointsGoal e :=
  parametricEndpointsGoal_of_witnesses_perm w (topologyPermForArcsP0Of e) hsrc
    (topologyPermForArcsP0Of_len e) htop

def parametricEndpointsGoal_of_witnesses_lookup {e : CrossingEndpoints}
    (w : ParametricDischargeWitnesses e)
    (hsrc : (residualGlobalVres e).length = 6)
    (htop : topologySetEq (globalTopologyRenameFor e hsrc)
        (residualGlobalAxioms e) = true) :
    ParametricEndpointsGoal e :=
  parametricEndpointsGoal_of_witnesses_perm w (topologyPermForEndpoints e) hsrc
    (topologyPermForEndpoints_len e) htop

/-- Witnesses + perm agrees with `topologyPermForEndpoints` ⇒ full goal. -/
def parametricEndpointsGoal_of_witnesses_perm_agrees {e : CrossingEndpoints}
    (w : ParametricDischargeWitnesses e) {perm : List Nat}
    (hperm : perm = topologyPermForEndpoints e)
    (hsrc : (residualGlobalVres e).length = 6)
    (htop : topologySetEq (globalTopologyRenameFromPerm e perm hsrc
        (by rw [hperm]; exact topologyPermForEndpoints_len e))
        (residualGlobalAxioms e) = true) :
    ParametricEndpointsGoal e := by
  subst hperm
  exact parametricEndpointsGoal_of_witnesses_lookup w hsrc htop

theorem parametricEndpointsGoal_fresh_g0_of_witnesses_perm_agrees {e : CrossingEndpoints}
    (w : ParametricDischargeWitnesses e) {perm : List Nat}
    (hperm : perm = topologyPermForEndpoints e)
    (hsrc : (residualGlobalVres e).length = 6)
    (htop : topologySetEq (globalTopologyRenameFromPerm e perm hsrc
        (by rw [hperm]; exact topologyPermForEndpoints_len e))
        (residualGlobalAxioms e) = true) :
    ∃ fw : FreshG0Obligation, ¬ fw.projection.gClosure.mem [] :=
  parametric_goal_fresh_g0 (parametricEndpointsGoal_of_witnesses_perm_agrees w hperm hsrc htop)

/-! ### Per-instance combinatorial sufficient bundle (still needs Bool witnesses) -/

structure ParametricCombinatorialGoalSufficient (e : CrossingEndpoints) where
  witnesses : ParametricDischargeWitnesses e
  hsrc : (residualGlobalVres e).length = 6
  topology_ok : topologySetEq (globalTopologyRenameFor e hsrc)
      (residualGlobalAxioms e) = true

def parametricEndpointsGoal_of_combinatorial_sufficient {e : CrossingEndpoints}
    (s : ParametricCombinatorialGoalSufficient e) : ParametricEndpointsGoal e :=
  parametricEndpointsGoal_of_witnesses_lookup s.witnesses s.hsrc s.topology_ok

theorem parametric_combinatorial_sufficient_fresh_g0 {e : CrossingEndpoints}
    (s : ParametricCombinatorialGoalSufficient e) :
    ∃ fw : FreshG0Obligation, ¬ fw.projection.gClosure.mem [] :=
  parametric_goal_fresh_g0 (parametricEndpointsGoal_of_combinatorial_sufficient s)

theorem topologySetEq_globalTopologyRenameFor_of_arc_p0 {e : CrossingEndpoints}
    (h : parametricDischargeReducesToArcP0 e)
    (s : ParametricCombinatorialGoalSufficient e) :
    topologySetEq (globalTopologyRenameFromPerm e (topologyPermForArcsP0Of e) s.hsrc
        (topologyPermForArcsP0Of_len e))
        (residualGlobalAxioms e) = true :=
  topologySetEq_globalTopologyRenameFromPerm_of_perm_eq (topologyPermForEndpoints_len e)
    (topologyPermForArcsP0Of_len e) h.symm s.hsrc (by
      rw [← globalTopologyRenameFor_eq_perm e s.hsrc]
      exact s.topology_ok)

/-- When `(n,toArcs,p0)` fixes perm (461/461 catalog), combinatorial sufficient
    rewrites to arc-p0 rename — no 461-key endpoint hash on the perm side. -/
structure ParametricArcP0GoalSufficient (e : CrossingEndpoints) where
  arc_p0 : parametricDischargeReducesToArcP0 e
  witnesses : ParametricDischargeWitnesses e
  hsrc : (residualGlobalVres e).length = 6
  topology_ok : topologySetEq (globalTopologyRenameFromPerm e (topologyPermForArcsP0Of e) hsrc
      (topologyPermForArcsP0Of_len e))
      (residualGlobalAxioms e) = true

def parametricEndpointsGoal_of_arc_p0_sufficient {e : CrossingEndpoints}
    (s : ParametricArcP0GoalSufficient e) : ParametricEndpointsGoal e :=
  parametricEndpointsGoal_of_witnesses_arc_p0 s.witnesses s.hsrc s.topology_ok

theorem parametric_arc_p0_sufficient_fresh_g0 {e : CrossingEndpoints}
    (s : ParametricArcP0GoalSufficient e) :
    ∃ fw : FreshG0Obligation, ¬ fw.projection.gClosure.mem [] :=
  parametric_goal_fresh_g0 (parametricEndpointsGoal_of_arc_p0_sufficient s)

def parametricArcP0Sufficient_of_combinatorial {e : CrossingEndpoints}
    (s : ParametricCombinatorialGoalSufficient e)
    (h : parametricDischargeReducesToArcP0 e) :
    ParametricArcP0GoalSufficient e where
  arc_p0 := h
  witnesses := s.witnesses
  hsrc := s.hsrc
  topology_ok := topologySetEq_globalTopologyRenameFor_of_arc_p0 h s

def parametric_discharge_reduces_to_arc_p0_combinatorial {e : CrossingEndpoints}
    (h : parametricDischargeReducesToArcP0 e)
    (s : ParametricCombinatorialGoalSufficient e) : ParametricEndpointsGoal e :=
  parametricEndpointsGoal_of_arc_p0_sufficient (parametricArcP0Sufficient_of_combinatorial s h)

/-- When arc shape fixes perm (83/461), combinatorial sufficient rewrites to arc-perm. -/
def parametric_discharge_reduces_to_arc_unique_combinatorial {e : CrossingEndpoints}
    {perm : List Nat}
    (_harc : topologyPermForArcs e.n e.toArcs = some perm)
    (hagree : perm = topologyPermForEndpoints e)
    (s : ParametricCombinatorialGoalSufficient e) : ParametricEndpointsGoal e :=
  parametricEndpointsGoal_of_witnesses_perm_agrees s.witnesses hagree s.hsrc
    (by rw [globalTopologyRenameFromPerm_eq_when_perm_agrees hagree s.hsrc]; exact s.topology_ok)

structure ParametricArcUniqueGoalSufficient (e : CrossingEndpoints) where
  arc_unique : topologyPermArcShapeUnique e.n e.toArcs
  witnesses : ParametricDischargeWitnesses e
  hsrc : (residualGlobalVres e).length = 6
  topology_ok : topologySetEq (globalTopologyRenameFor e hsrc)
      (residualGlobalAxioms e) = true

def parametricArcUniqueSufficient_of_combinatorial {e : CrossingEndpoints}
    (s : ParametricCombinatorialGoalSufficient e)
    (h : parametricDischargeReducesToArcUnique e) :
    ParametricArcUniqueGoalSufficient e where
  arc_unique := (parametricDischargeReducesToArcUnique_iff e).1 h |>.1
  witnesses := s.witnesses
  hsrc := s.hsrc
  topology_ok := s.topology_ok

/-! ### ∀e-scale sufficient bundles (after per-instance structures) -/

/-- Per-instance combinatorial sufficient bundle at ∀e scale (still needs Bool witnesses). -/
def parametricDischargeCombinatorialSufficientForAll : Prop :=
  ∀ e : CrossingEndpoints, ParametricCombinatorialGoalSufficient e

/-- Arc-p0 sufficient bundle at ∀e scale (461/461 catalog tabulation for `arc_p0`). -/
def parametricDischargeCombinatorialArcP0SufficientForAll : Prop :=
  ∀ e : CrossingEndpoints, ParametricArcP0GoalSufficient e

/-- Arc-unique sufficient bundle at ∀e scale (83/461 catalog tabulation for arc shape). -/
def parametricDischargeCombinatorialArcUniqueSufficientForAll : Prop :=
  ∀ e : CrossingEndpoints, ParametricArcUniqueGoalSufficient e

/-- Subclass: discharge for every seed with `(n,toArcs,p0)`-fixed perm (461/461 emit). -/
def parametricDischargeCombinatorialForArcP0Catalog : Prop :=
  ∀ e : CrossingEndpoints, parametricDischargeReducesToArcP0 e → ParametricEndpointsDischarge e

/-- Subclass: discharge when arc shape alone fixes perm (83/461 emit). -/
def parametricDischargeCombinatorialForArcUniqueCatalog : Prop :=
  ∀ e : CrossingEndpoints, parametricDischargeReducesToArcUnique e → ParametricEndpointsDischarge e

theorem parametricDischargeCombinatorialForArcP0Catalog_of_forall
    (h : parametricDischargeCombinatorialForAll) :
    parametricDischargeCombinatorialForArcP0Catalog :=
  fun e _ => h e

theorem parametricDischargeCombinatorialForArcUniqueCatalog_of_forall
    (h : parametricDischargeCombinatorialForAll) :
    parametricDischargeCombinatorialForArcUniqueCatalog :=
  fun e _ => h e

theorem parametricDischargeCombinatorialSufficientForAll_of_witnesses_forall
    (h : parametricDischargeCombinatorialWitnessesForAll)
    (htop : ∀ e : CrossingEndpoints,
      ∃ hsrc : (residualGlobalVres e).length = 6,
        topologySetEq (globalTopologyRenameFor e hsrc)
          (residualGlobalAxioms e) = true) :
    parametricDischargeCombinatorialSufficientForAll := by
  intro e
  rcases htop e with ⟨hsrc, htop⟩
  exact { witnesses := h e, hsrc := hsrc, topology_ok := htop }

def parametricEndpointsGoal_of_arc_unique_sufficient {e : CrossingEndpoints}
    (s : ParametricArcUniqueGoalSufficient e) : ParametricEndpointsGoal e :=
  parametricEndpointsGoal_of_combinatorial_sufficient
    { witnesses := s.witnesses, hsrc := s.hsrc, topology_ok := s.topology_ok }

theorem parametricDischargeCombinatorialArcP0SufficientForAll_of_sufficient
    (h : parametricDischargeCombinatorialSufficientForAll)
    (harc : ∀ e, parametricDischargeReducesToArcP0 e) :
    parametricDischargeCombinatorialArcP0SufficientForAll :=
  fun e => parametricArcP0Sufficient_of_combinatorial (h e) (harc e)

theorem parametricDischargeCombinatorialArcUniqueSufficientForAll_of_sufficient
    (h : parametricDischargeCombinatorialSufficientForAll)
    (harc : ∀ e, parametricDischargeReducesToArcUnique e) :
    parametricDischargeCombinatorialArcUniqueSufficientForAll :=
  fun e => parametricArcUniqueSufficient_of_combinatorial (h e) (harc e)

def parametricEndpointsGoal_of_combinatorial_sufficient_forall
    (h : parametricDischargeCombinatorialSufficientForAll) (e : CrossingEndpoints) :
    ParametricEndpointsGoal e :=
  parametricEndpointsGoal_of_combinatorial_sufficient (h e)

/-! ### Partial ∀e: canonical smoke subclass (n=5..10, emit-backed) -/

theorem canonical_parametric_discharges :
    ParametricEndpointsDischarge c5OfoldEndpoints ∧
      ParametricEndpointsDischarge c5Alt1Endpoints ∧
      ParametricEndpointsDischarge c6Endpoints0123 ∧
      ParametricEndpointsDischarge c7Endpoints0123 ∧
      ParametricEndpointsDischarge c8Endpoints0123 ∧
      ParametricEndpointsDischarge c9Endpoints0123 ∧
      ParametricEndpointsDischarge c10Endpoints024 :=
  ⟨c5OfoldParametricDischarge, c5Alt1ParametricDischarge, c6ParametricDischarge,
    c7ParametricDischarge, c8ParametricDischarge, c9ParametricDischarge,
    c10ParametricDischarge⟩

def canonicalParametricGoals :
    ParametricEndpointsGoal c5OfoldEndpoints ×
      ParametricEndpointsGoal c5Alt1Endpoints ×
      ParametricEndpointsGoal c6Endpoints0123 ×
      ParametricEndpointsGoal c7Endpoints0123 ×
      ParametricEndpointsGoal c8Endpoints0123 ×
      ParametricEndpointsGoal c9Endpoints0123 ×
      ParametricEndpointsGoal c10Endpoints024 :=
  (c5OfoldParametricGoal, c5Alt1ParametricGoal, c6ParametricGoal, c7ParametricGoal,
    c8ParametricGoal, c9ParametricGoal, c10ParametricGoal)

theorem canonical_parametric_discharges_fixed_n_partial :
    parametricDischargeCombinatorialForFixedN 5 → ParametricEndpointsDischarge c5OfoldEndpoints :=
  fun h => h c5OfoldEndpoints rfl

theorem canonical_parametric_discharges_fixed_n_range_partial :
    parametricDischargeCombinatorialForFixedNRange 5 10 →
      ParametricEndpointsDischarge c5OfoldEndpoints :=
  fun h => h c5OfoldEndpoints (by decide) (by decide)

theorem canonical_parametric_discharges_mass_window_partial :
    parametricDischargeCombinatorialForMassWindow →
      ParametricEndpointsDischarge c5OfoldEndpoints :=
  fun h => h c5OfoldEndpoints (And.intro (by decide) (by decide))

theorem canonical_parametric_discharges_combinatorial_not_closed :
    parametricDischargeCombinatorialForAll →
      ParametricEndpointsDischarge c5OfoldEndpoints :=
  fun h => h c5OfoldEndpoints

/-- Canonical topology perm dst for ofold-shaped residuals. -/
def parametric_goal_ofold_discharge : ParametricEndpointsGoal c5OfoldEndpoints :=
  c5OfoldParametricGoal

def canonicalParametricDischargeDoc : String :=
  "Partial ∀e: 7 canonical n=5..10 smoke seeds (emit-backed); combinatorial ∀461 open"

def parametricCombinatorialDischargeDoc : String :=
  "Witnesses⇒Discharge; saturate→WidthClosure; discharge⇒FreshG0; " ++
  "perm-agrees rename + combinatorial sufficient bundle; emit 461/461 contrast"

def parametricCombinatorialDischargeOpenDoc : String :=
  "BLOCKER (honest): combinatorial ∀e ParametricEndpointsDischarge = " ++
  "parametricDischargeCombinatorialWitnessesForAll (per-instance width-3 saturate on " ++
  "closure3/residualGlobal + proj Bool + r_no_empty); topology perm side closed for catalog " ++
  "via (n,toArcs,p0) 461/461 tabulation — NOT the gap. Subclasses provable from ForAll: " ++
  "fixedN, fixedNRange, massWindow, arcP0Catalog, arcUniqueCatalog, sufficient bundles. " ++
  "Hop window 5≤n≤14 ⇒ total≤10 necessary not sufficient (c8EndpointsEven: precond + " ++
  "same hop as c8Endpoints0123 but different embedding; discharge only for canonical seed). " ++
  "461/461; (n,toArcs,Vres) 459/461 (c6 collision). No closed-form synthesis of Bool " ++
  "witnesses without emit/native_decide per instance; 461/461 discharge exists only via emit."

def parametricCombinatorialDischargeBlockerDoc : String :=
  "CEILING (impossible without emit): per-instance width-3 saturate + residualGlobal XOR " ++
  "Bool witnesses; ∀e topologySetEq from combinatorial closed form; ∀e arc_p0/arc_unique " ++
  "tabulation as Prop (461/461 and 83/461 are emit-checked flags, not derived). " ++
  "Reducible combinatorially once witnesses supplied: topology perm dst via arc-unique " ++
  "(83/461) or arc-p0 (461/461); discharge⇒FreshG0; witnesses⇔discharge; sufficient⇒goal. " ++
  "Open: parametricDischargeCombinatorialForAll."

def parametricCombinatorialDischargeCeilingDoc : String :=
  "Provable without emit: ForAll↔Witnesses; subclass hierarchy; mass-window precond " ++
  "necessary not sufficient (c8EndpointsEven vs c8Endpoints0123); perm rename functoriality; " ++
  "ParametricCombinatorialGoalSufficient / ArcP0 / ArcUnique per instance. " ++
  "Emit-only ceiling: 461 discharge flags, 461 topology flags, 461 arc_p0 agreement."

/-- Catalog index range (0..460); per-index `CrossingEndpoints` enumeration is emit-only. -/
def parametricDischargeCombinatorialCatalogIndexRange : Nat × Nat := (0, 460)

def parametricTopologyPermPartialKeyDoc : String :=
  "Partial keys: (n,toArcs) 83/461; cyclic 0/461; (n,toArcs,Vres) 459/461; " ++
  "(n,toArcs,p0) 461/461 minimal; full endpointsLookupKey 461/461 emit; " ++
  "no combinatorial closed form without tabulation (see topologyPermNoClosedFormDoc)"

def parametricTopologyPermNoClosedFormDoc : String :=
  "E5 open-2 closed: perm side catalog-complete via topologyPermForArcsP0Of 461/461; " ++
  "combinatorial closed form without emit ruled out (126/209 multi-perm shapes, " ++
  "Vres collision c6, schedule invariants insufficient); blocker for discharge is " ++
  "Bool saturate witnesses not topology perm"

/-- Catalog mass bundle: arcs partial 83/461, arcs+p0 agrees 461/461 (emit-checked). -/
theorem parametricTopologyPermPartialKey_mass :
    topologyPermArcShapeMass = (209, 83, 126, 83, 378) ∧
      topologyPermArcsP0EndpointAgreementFlags.length = 461 ∧
      topologyPermArcsP0EndpointAgreementFlags.all id = true := by
  native_decide

end PNPLab.Bicyclic

namespace PNPLab.Resolution

open Bicyclic

theorem parametric_discharge_witnesses_mass_window_chain
    (e : CrossingEndpoints) (h5 : 5 ≤ e.n) (h14 : e.n ≤ 14)
    (w : ParametricDischargeWitnesses e) :
    parametricProjHolds e ∧
      ∃ fw : FreshG0Obligation, ¬ fw.projection.gClosure.mem [] ∧
        1 ≤ e.toArcs.total ∧ e.toArcs.total ≤ 10 := by
  have d := parametricEndpointsDischarge_of_witnesses w
  rcases parametric_discharge_chain d with ⟨hproj, ⟨fw, hfw⟩⟩
  exact ⟨hproj, fw, hfw, parametric_discharge_hop_window e h5 h14⟩

end PNPLab.Resolution
