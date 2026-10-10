/-
  K₄ residual catalog (Category C / G3–G5 bridge).

  After the crossing fold schedule completes, the four-arc count sketch is
  uniquely the K₄ skeleton (`k4CrossingArcs`).   Concrete packs (OneFold…TenFold)
  then supply the syntactic `Closure₃` witness on 16 XOR axioms (`k4Closure`).

  This file does **not** identify variable renamings across instances — only the
  combinatorial hop budget and the shared K₄ closure template.
-/

import PNPLab.CrossingFoldSchedule
import PNPLab.K4Width3

namespace PNPLab.Bicyclic

/-- Canonical empty four-arc crossing skeleton (K₄ branch contraction done). -/
abbrev K4Skeleton : CrossingArcs := k4CrossingArcs

theorem K4Skeleton_total_zero : K4Skeleton.total = 0 :=
  k4CrossingArcs_done

/-- A crossing residual with zero internals is uniquely the K₄ skeleton. -/
theorem total_zero_iff_k4 (c : CrossingArcs) :
    c.total = 0 ↔ c = K4Skeleton := by
  constructor
  · intro h
    cases c with
    | mk a0 a1 a2 a3 =>
      simp [CrossingArcs.total] at h
      have ha0 : a0 = 0 := by omega
      have ha1 : a1 = 0 := by omega
      have ha2 : a2 = 0 := by omega
      have ha3 : a3 = 0 := by omega
      simp [K4Skeleton, k4CrossingArcs, ha0, ha1, ha2, ha3]
  · intro h
    simp [h, K4Skeleton, k4CrossingArcs, CrossingArcs.total]

/-- Schedule completion lands on the unique K₄ skeleton. -/
theorem reaches_k4_skeleton (c : CrossingArcs) :
    c.foldIter c.total = K4Skeleton := by
  have hz : (c.foldIter c.total).total = 0 := c.reaches_k4
  exact (total_zero_iff_k4 (c.foldIter c.total)).mp hz

/-- Hop budget for the multihop schedule = initial total internals (E2: tips = total). -/
def hopBudget (c : CrossingArcs) : Nat :=
  c.stepsToK4

theorem hopBudget_eq_total (c : CrossingArcs) :
    hopBudget c = c.total :=
  c.stepsToK4_eq

/-- Mass upper bound: crossing n=5..10 uses at most 6 tips (`multihop_chains_full.json`). -/
def maxCrossingHopBudget : Nat := 10

theorem c6_hop_budget : hopBudget c6CrossingArcs = 4 :=
  c6_stepsToK4

/-- Resolution-side K₄ template after combinatorial schedule (lower bound). -/
def k4TemplateClosure : Resolution.WidthClosure 3 :=
  Resolution.k4Closure

theorem k4_template_axiom_count : Resolution.k4Axioms.length = 16 := by
  native_decide

theorem k4_template_no_empty : ¬ k4TemplateClosure.mem [] :=
  Resolution.k4_no_empty

/--
  Catalog entry: combinatorial schedule complete ⇒ skeleton + hop count + template
  closure size (syntactic identification to a concrete pack is still per-instance).
-/
structure K4CatalogWitness where
  arcs : CrossingArcs
  hops : Nat
  hops_eq_total : hops = arcs.total
  skeleton : arcs.foldIter hops = K4Skeleton
  closureSize : Nat := 16
  size_ok : closureSize = Resolution.k4Axioms.length

/-- Build a catalog witness from any crossing arc sketch. -/
def catalogWitness (c : CrossingArcs) : K4CatalogWitness where
  arcs := c
  hops := c.total
  hops_eq_total := rfl
  skeleton := reaches_k4_skeleton c
  closureSize := 16
  size_ok := k4_template_axiom_count

theorem catalogWitness_hops (c : CrossingArcs) :
    (catalogWitness c).hops = hopBudget c := by
  simp [catalogWitness, hopBudget, CrossingArcs.stepsToK4]

def k4CatalogDoc : String :=
  "papers/FAMILY_PROJECTION_E5.md"

def k4LowerBoundDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-CYCLE-TWO-CHORDS-001/LIFT_K4.md"

end PNPLab.Bicyclic
