/-
  Parametric Closure₃ outline (Category C / G5).

  What is closed:
  - Crossing schedule ∀ → K₄ skeleton (`reaches_k4_skeleton`)
  - Hop budget ∈[1,6] → pack family (`CrossingPackCatalog`)
  - Pack residuals ≅ `k4Closed` up to topology rename (G3)
  - Topology iso transfers □-freedom from the template

  What remains open (true parametric gap):
  - Synthesize the residual axiom list + Closure₃ for an *arbitrary*
    crossing instance (not one of the six pack witnesses), then discharge
    topology set-eq without `native_decide` on that instance.

  This module records the transfer lemmas that any future parametric
  synthesis must reuse.
-/

import PNPLab.CrossingPackCatalog
import PNPLab.MembershipTransport

namespace PNPLab.Resolution

/-- Empty clause is fixed by any variable rename. -/
theorem rename_preserves_empty (r : VarRename) :
    r.renameClause [] = some [] :=
  VarRename.renameClause_empty r

/-- `sameClause [] D` holds iff `D` is empty. -/
theorem sameClause_empty_iff (D : Clause) :
    sameClause [] D = true ↔ D = [] := by
  constructor
  · intro h
    simp only [sameClause, List.all_nil, Bool.true_and] at h
    -- h : D.all (fun ℓ => [].contains ℓ) = true
    cases D with
    | nil => rfl
    | cons ℓ rest =>
      simp only [List.all_cons, List.contains_nil, Bool.false_and] at h
      cases h
  · intro h
    subst h
    native_decide

/-- Topology subset into `k4Closed` forbids □ in the source residual. -/
theorem renamedSubset_no_empty
    (r : VarRename) (S : List Clause)
    (h : renamedSubset r S k4Closed = true) :
    ¬ ([] ∈ S) := by
  intro hempty
  have hall := List.all_eq_true.mp h
  have hC := hall [] hempty
  -- hC : match r.renameClause [] with | none => false | some C' => k4Closed.any (sameClause C')
  rw [rename_preserves_empty] at hC
  have hex : ∃ C ∈ k4Closed, sameClause [] C = true :=
    List.any_eq_true.mp hC
  obtain ⟨C, hCmem, hsame⟩ := hex
  have hCempty : C = [] := (sameClause_empty_iff C).mp hsame
  subst hCempty
  exact k4_no_empty hCmem

/-- Pack-family topology set-eq ⇒ residual has no □ (via rename). -/
theorem pack_topology_no_empty_source (f : CrossingPackFamily) :
    match f with
    | .oneFold => ¬ ([] ∈ ofoldRClosed)
    | .multiFold => ¬ ([] ∈ mfRClosed)
    | .tripleFold => ¬ ([] ∈ tfRClosed)
    | .fourFold => ¬ ([] ∈ ffRClosed)
    | .fiveFold => ¬ ([] ∈ xfRClosed)
    | .sixFold => ¬ ([] ∈ sfRClosed)
    | .sevenFold => ¬ ([] ∈ vfRClosed)
    | .eightFold => ¬ ([] ∈ efRClosed)
    | .nineFold => ¬ ([] ∈ nfRClosed)
    | .tenFold => ¬ ([] ∈ zfRClosed) := by
  cases f with
  | oneFold =>
    intro h
    exact ofoldR_no_empty h
  | multiFold =>
    exact renamedSubset_no_empty mfTopologyRename mfRClosed (by
      have := mfTopologySetEq_true
      simp [mfTopologySetEq] at this
      exact this.1)
  | tripleFold =>
    exact renamedSubset_no_empty tfTopologyRename tfRClosed (by
      have := tfTopologySetEq_true
      simp [tfTopologySetEq] at this
      exact this.1)
  | fourFold =>
    exact renamedSubset_no_empty ffTopologyRename ffRClosed (by
      have := ffTopologySetEq_true
      simp [ffTopologySetEq] at this
      exact this.1)
  | fiveFold =>
    exact renamedSubset_no_empty xfTopologyRename xfRClosed (by
      have := xfTopologySetEq_true
      simp [xfTopologySetEq] at this
      exact this.1)
  | sixFold =>
    exact renamedSubset_no_empty sfTopologyRename sfRClosed (by
      have := sfTopologySetEq_true
      simp [sfTopologySetEq] at this
      exact this.1)
  | sevenFold =>
    exact renamedSubset_no_empty vfTopologyRename vfRClosed (by
      have := vfTopologySetEq_true
      simp [vfTopologySetEq] at this
      exact this.1)
  | eightFold =>
    exact renamedSubset_no_empty efTopologyRename efRClosed (by
      have := efTopologySetEq_true
      simp [efTopologySetEq] at this
      exact this.1)
  | nineFold =>
    exact renamedSubset_no_empty nfTopologyRename nfRClosed (by
      have := nfTopologySetEq_true
      simp [nfTopologySetEq] at this
      exact this.1)
  | tenFold =>
    exact renamedSubset_no_empty zfTopologyRename zfRClosed (by
      have := zfTopologySetEq_true
      simp [zfTopologySetEq] at this
      exact this.1)

/--
  G5 discharge checklist for a future parametric instance:
  schedule done, hops in window, pack family chosen, topology set-eq, no □.
-/
structure ParametricClosure3Goal where
  arcs : Bicyclic.CrossingArcs
  hops_in_window : 1 ≤ arcs.total ∧ arcs.total ≤ 10
  skeleton : arcs.foldIter arcs.total = Bicyclic.K4Skeleton
  family : CrossingPackFamily
  family_ok : packFamilyOfHops arcs.total = some family
  topology_ok : packTopologySetEq family = true
  g_no_empty : ¬ (packProjection family).gClosure.mem []

/-- Concrete C₆ instance meets the parametric checklist via FourFold. -/
def c6ParametricGoal : ParametricClosure3Goal where
  arcs := Bicyclic.c6CrossingArcs
  hops_in_window := by decide
  skeleton := Bicyclic.reaches_k4_skeleton Bicyclic.c6CrossingArcs
  family := .fourFold
  family_ok := rfl
  topology_ok := by native_decide
  g_no_empty := pack_no_empty_of_projection .fourFold

/-- Every hop budget in the mass window yields a completed checklist
    against the catalog packs (not a fresh Closure₃ synthesis). -/
theorem parametric_goal_from_arcs
    (c : Bicyclic.CrossingArcs)
    (hLo : 1 ≤ c.total) (hHi : c.total ≤ 10) :
    ∃ g : ParametricClosure3Goal, g.arcs = c := by
  obtain ⟨f, hf, htop, hne⟩ := crossing_pack_route (h := c.total) hLo hHi
  refine ⟨{
    arcs := c
    hops_in_window := ⟨hLo, hHi⟩
    skeleton := Bicyclic.reaches_k4_skeleton c
    family := f
    family_ok := hf
    topology_ok := htop
    g_no_empty := hne
  }, rfl⟩

/-- Remaining open obligation (documentation hook).
  ofoldR `k4ClosedUnder` Prop-lifted via `List.Perm` (`ofoldR_closed_via_perm`).
  Packs mf..sf and alts 1..6 closed via exact or norm-rename Prop pullback.
  Hop window covers all-odd mass n≤14 (TenFold); `ResidualSynthWitness` packs OK.
  Open: residualAxioms without pack lookup; Mathlib `IsOuterplanar`. -/
def parametricClosure3OpenDoc : String :=
  "parametric ProjectionInclusion c5 (CrossingEndpointsParametricProjection); " ++
  "open: Closure₃(G_e) ∀e; signed VarRename; Mathlib IsOuterplanar."


def parametricOutlineDoc : String :=
  "papers/FAMILY_PROJECTION_E5.md"

end PNPLab.Resolution
