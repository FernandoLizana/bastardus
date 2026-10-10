/-
  Closure₃-routing: CrossingEndpoints → EliminationStep (Category C).

  Hop budget 1 ⇔ `n = 5` ⇔ `oneFold` pack.
  Hop budget 2 ⇔ `n = 6` ⇔ `multiFold` pack.
  Reuses existing pack `EliminationStep`s — parametric *routing*, not fresh
  WidthClosure synthesis.
-/

import PNPLab.CrossingChordsToArcs
import PNPLab.CrossingPackCatalog
import PNPLab.OuterplanarFoldBridge
import PNPLab.ParametricClosure3

namespace PNPLab

open Outerplanar Resolution
open Bicyclic

/-- Hop-1 crossings route to the OneFold pack family. -/
theorem CrossingEndpoints.routes_oneFold (e : CrossingEndpoints)
    (h : e.toArcs.total = 1) :
    packFamilyOfHops e.toArcs.total = some .oneFold := by
  rw [h]
  rfl

/-- Hop-2 crossings route to the MultiFold pack family. -/
theorem CrossingEndpoints.routes_multiFold (e : CrossingEndpoints)
    (h : e.toArcs.total = 2) :
    packFamilyOfHops e.toArcs.total = some .multiFold := by
  rw [h]
  rfl

/-- Parametric first-hop elimination step (OneFold witness). -/
def CrossingEndpoints.firstHopElim (e : CrossingEndpoints)
    (_h : e.toArcs.total = 1) : EliminationStep 3 :=
  ofoldEliminationStep

/-- Parametric second-hop elimination step (MultiFold first link). -/
def CrossingEndpoints.secondHopElim (e : CrossingEndpoints)
    (_h : e.toArcs.total = 2) : EliminationStep 3 :=
  mfStep01

theorem CrossingEndpoints.total_eq_one_of_n5 (e : CrossingEndpoints)
    (h5 : e.n = 5) : e.toArcs.total = 1 := by
  rw [CrossingEndpoints.toArcs_total, h5]

theorem CrossingEndpoints.total_eq_two_of_n6 (e : CrossingEndpoints)
    (h6 : e.n = 6) : e.toArcs.total = 2 := by
  rw [CrossingEndpoints.toArcs_total, h6]

/-- Parametric Closure₃ checklist for every hop-1 endpoint configuration. -/
theorem CrossingEndpoints.parametric_goal_hop1 (e : CrossingEndpoints)
    (h : e.toArcs.total = 1) :
    ∃ g : ParametricClosure3Goal, g.arcs = e.toArcs ∧ g.family = .oneFold := by
  obtain ⟨g, hg⟩ := parametric_goal_from_arcs e.toArcs (by omega) (by omega)
  have hf := g.family_ok
  have ht : packFamilyOfHops e.toArcs.total = some CrossingPackFamily.oneFold :=
    CrossingEndpoints.routes_oneFold e h
  refine ⟨g, hg, ?_⟩
  rw [hg] at hf
  exact Option.some_inj.mp (hf.symm.trans ht)

/-- Parametric Closure₃ checklist for every hop-2 endpoint configuration. -/
theorem CrossingEndpoints.parametric_goal_hop2 (e : CrossingEndpoints)
    (h : e.toArcs.total = 2) :
    ∃ g : ParametricClosure3Goal, g.arcs = e.toArcs ∧ g.family = .multiFold := by
  obtain ⟨g, hg⟩ := parametric_goal_from_arcs e.toArcs (by omega) (by omega)
  have hf := g.family_ok
  have ht : packFamilyOfHops e.toArcs.total = some CrossingPackFamily.multiFold :=
    CrossingEndpoints.routes_multiFold e h
  refine ⟨g, hg, ?_⟩
  rw [hg] at hf
  exact Option.some_inj.mp (hf.symm.trans ht)

/-- Bundle: endpoints → oneFold route → FoldTipElimination tip + □-free step. -/
theorem CrossingEndpoints.hop1_elim_bundle (e : CrossingEndpoints)
    (h : e.toArcs.total = 1) :
    packFamilyOfHops e.toArcs.total = some .oneFold ∧
      (CrossingEndpoints.firstHopElim e h) = ofoldEliminationStep ∧
      ¬ (CrossingEndpoints.firstHopElim e h).before.mem [] ∧
      ¬ (CrossingEndpoints.firstHopElim e h).after.mem [] ∧
      (foldTipFirstHop .oneFold).tipKind = EarTipKind.shortcutDeg2NextToDeg3 :=
  ⟨CrossingEndpoints.routes_oneFold e h, rfl, ofoldG_no_empty, ofoldR_no_empty, rfl⟩

/-- Bundle: endpoints → multiFold route → first MultiFold elim + □-free step. -/
theorem CrossingEndpoints.hop2_elim_bundle (e : CrossingEndpoints)
    (h : e.toArcs.total = 2) :
    packFamilyOfHops e.toArcs.total = some .multiFold ∧
      (CrossingEndpoints.secondHopElim e h) = mfStep01 ∧
      ¬ (CrossingEndpoints.secondHopElim e h).before.mem [] ∧
      ¬ (CrossingEndpoints.secondHopElim e h).after.mem [] :=
  ⟨CrossingEndpoints.routes_multiFold e h, rfl, mfG0_no_empty, mfG1_no_empty⟩

/-- Hop-3..6 route to Triple/Four/Five/SixFold. -/
theorem CrossingEndpoints.routes_tripleFold (e : CrossingEndpoints)
    (h : e.toArcs.total = 3) :
    packFamilyOfHops e.toArcs.total = some .tripleFold := by
  rw [h]; rfl

theorem CrossingEndpoints.routes_fourFold (e : CrossingEndpoints)
    (h : e.toArcs.total = 4) :
    packFamilyOfHops e.toArcs.total = some .fourFold := by
  rw [h]; rfl

theorem CrossingEndpoints.routes_fiveFold (e : CrossingEndpoints)
    (h : e.toArcs.total = 5) :
    packFamilyOfHops e.toArcs.total = some .fiveFold := by
  rw [h]; rfl

theorem CrossingEndpoints.routes_sixFold (e : CrossingEndpoints)
    (h : e.toArcs.total = 6) :
    packFamilyOfHops e.toArcs.total = some .sixFold := by
  rw [h]; rfl

theorem CrossingEndpoints.routes_sevenFold (e : CrossingEndpoints)
    (h : e.toArcs.total = 7) :
    packFamilyOfHops e.toArcs.total = some .sevenFold := by
  rw [h]; rfl

theorem CrossingEndpoints.routes_eightFold (e : CrossingEndpoints)
    (h : e.toArcs.total = 8) :
    packFamilyOfHops e.toArcs.total = some .eightFold := by
  rw [h]; rfl

theorem CrossingEndpoints.routes_nineFold (e : CrossingEndpoints)
    (h : e.toArcs.total = 9) :
    packFamilyOfHops e.toArcs.total = some .nineFold := by
  rw [h]; rfl

theorem CrossingEndpoints.routes_tenFold (e : CrossingEndpoints)
    (h : e.toArcs.total = 10) :
    packFamilyOfHops e.toArcs.total = some .tenFold := by
  rw [h]; rfl

def CrossingEndpoints.thirdHopElim (e : CrossingEndpoints)
    (_h : e.toArcs.total = 3) : EliminationStep 3 :=
  tfStep01

def CrossingEndpoints.fourthHopElim (e : CrossingEndpoints)
    (_h : e.toArcs.total = 4) : EliminationStep 3 :=
  ffStep01

def CrossingEndpoints.fifthHopElim (e : CrossingEndpoints)
    (_h : e.toArcs.total = 5) : EliminationStep 3 :=
  xfStep01

def CrossingEndpoints.sixthHopElim (e : CrossingEndpoints)
    (_h : e.toArcs.total = 6) : EliminationStep 3 :=
  sfStep01

def CrossingEndpoints.seventhHopElim (e : CrossingEndpoints)
    (_h : e.toArcs.total = 7) : EliminationStep 3 :=
  vfStep01

def CrossingEndpoints.eighthHopElim (e : CrossingEndpoints)
    (_h : e.toArcs.total = 8) : EliminationStep 3 :=
  efStep01

def CrossingEndpoints.ninthHopElim (e : CrossingEndpoints)
    (_h : e.toArcs.total = 9) : EliminationStep 3 :=
  nfStep01

def CrossingEndpoints.tenthHopElim (e : CrossingEndpoints)
    (_h : e.toArcs.total = 10) : EliminationStep 3 :=
  zfStep01

theorem CrossingEndpoints.hop3_elim_bundle (e : CrossingEndpoints)
    (h : e.toArcs.total = 3) :
    packFamilyOfHops e.toArcs.total = some .tripleFold ∧
      (CrossingEndpoints.thirdHopElim e h) = tfStep01 ∧
      ¬ (CrossingEndpoints.thirdHopElim e h).before.mem [] ∧
      ¬ (CrossingEndpoints.thirdHopElim e h).after.mem [] :=
  ⟨CrossingEndpoints.routes_tripleFold e h, rfl, tfG0_no_empty, tfG1_no_empty⟩

theorem CrossingEndpoints.hop4_elim_bundle (e : CrossingEndpoints)
    (h : e.toArcs.total = 4) :
    packFamilyOfHops e.toArcs.total = some .fourFold ∧
      (CrossingEndpoints.fourthHopElim e h) = ffStep01 ∧
      ¬ (CrossingEndpoints.fourthHopElim e h).before.mem [] ∧
      ¬ (CrossingEndpoints.fourthHopElim e h).after.mem [] :=
  ⟨CrossingEndpoints.routes_fourFold e h, rfl, ffG0_no_empty, ffG1_no_empty⟩

theorem CrossingEndpoints.hop5_elim_bundle (e : CrossingEndpoints)
    (h : e.toArcs.total = 5) :
    packFamilyOfHops e.toArcs.total = some .fiveFold ∧
      (CrossingEndpoints.fifthHopElim e h) = xfStep01 ∧
      ¬ (CrossingEndpoints.fifthHopElim e h).before.mem [] ∧
      ¬ (CrossingEndpoints.fifthHopElim e h).after.mem [] :=
  ⟨CrossingEndpoints.routes_fiveFold e h, rfl, xfG0_no_empty, xfG1_no_empty⟩

theorem CrossingEndpoints.hop6_elim_bundle (e : CrossingEndpoints)
    (h : e.toArcs.total = 6) :
    packFamilyOfHops e.toArcs.total = some .sixFold ∧
      (CrossingEndpoints.sixthHopElim e h) = sfStep01 ∧
      ¬ (CrossingEndpoints.sixthHopElim e h).before.mem [] ∧
      ¬ (CrossingEndpoints.sixthHopElim e h).after.mem [] :=
  ⟨CrossingEndpoints.routes_sixFold e h, rfl, sfG0_no_empty, sfG1_no_empty⟩

theorem CrossingEndpoints.hop7_elim_bundle (e : CrossingEndpoints)
    (h : e.toArcs.total = 7) :
    packFamilyOfHops e.toArcs.total = some .sevenFold ∧
      (CrossingEndpoints.seventhHopElim e h) = vfStep01 ∧
      ¬ (CrossingEndpoints.seventhHopElim e h).before.mem [] ∧
      ¬ (CrossingEndpoints.seventhHopElim e h).after.mem [] :=
  ⟨CrossingEndpoints.routes_sevenFold e h, rfl, vfG0_no_empty, vfG1_no_empty⟩

theorem CrossingEndpoints.hop8_elim_bundle (e : CrossingEndpoints)
    (h : e.toArcs.total = 8) :
    packFamilyOfHops e.toArcs.total = some .eightFold ∧
      (CrossingEndpoints.eighthHopElim e h) = efStep01 ∧
      ¬ (CrossingEndpoints.eighthHopElim e h).before.mem [] ∧
      ¬ (CrossingEndpoints.eighthHopElim e h).after.mem [] :=
  ⟨CrossingEndpoints.routes_eightFold e h, rfl, efG0_no_empty, efG1_no_empty⟩

theorem CrossingEndpoints.hop9_elim_bundle (e : CrossingEndpoints)
    (h : e.toArcs.total = 9) :
    packFamilyOfHops e.toArcs.total = some .nineFold ∧
      (CrossingEndpoints.ninthHopElim e h) = nfStep01 ∧
      ¬ (CrossingEndpoints.ninthHopElim e h).before.mem [] ∧
      ¬ (CrossingEndpoints.ninthHopElim e h).after.mem [] :=
  ⟨CrossingEndpoints.routes_nineFold e h, rfl, nfG0_no_empty, nfG1_no_empty⟩

theorem CrossingEndpoints.hop10_elim_bundle (e : CrossingEndpoints)
    (h : e.toArcs.total = 10) :
    packFamilyOfHops e.toArcs.total = some .tenFold ∧
      (CrossingEndpoints.tenthHopElim e h) = zfStep01 ∧
      ¬ (CrossingEndpoints.tenthHopElim e h).before.mem [] ∧
      ¬ (CrossingEndpoints.tenthHopElim e h).after.mem [] :=
  ⟨CrossingEndpoints.routes_tenFold e h, rfl, zfG0_no_empty, zfG1_no_empty⟩

/-- Canonical C₅ endpoints `{0,1,2,3}` on C₅. -/
def c5Endpoints0123 : CrossingEndpoints where
  n := 5
  p0 := 0
  p1 := 1
  p2 := 2
  p3 := 3
  ordered := by decide

theorem c5Endpoints0123_hop1 :
    c5Endpoints0123.toArcs.total = 1 := by
  native_decide

theorem c5Endpoints_hop1_bundle :
    packFamilyOfHops c5Endpoints0123.toArcs.total = some .oneFold ∧
      ¬ (CrossingEndpoints.firstHopElim c5Endpoints0123 c5Endpoints0123_hop1).before.mem [] :=
  let h := CrossingEndpoints.hop1_elim_bundle c5Endpoints0123 c5Endpoints0123_hop1
  ⟨h.1, h.2.2.1⟩

theorem c6Endpoints0123_hop2 :
    c6Endpoints0123.toArcs.total = 2 :=
  c6Endpoints0123_total

theorem c6Endpoints_hop2_bundle :
    packFamilyOfHops c6Endpoints0123.toArcs.total = some .multiFold ∧
      ¬ (CrossingEndpoints.secondHopElim c6Endpoints0123 c6Endpoints0123_hop2).before.mem [] :=
  let h := CrossingEndpoints.hop2_elim_bundle c6Endpoints0123 c6Endpoints0123_hop2
  ⟨h.1, h.2.2.1⟩

/-- Canonical endpoints `{0,1,2,3}` on C₇..C₁₄ ⇒ hop budgets 3..10. -/
def c7Endpoints0123 : CrossingEndpoints where
  n := 7; p0 := 0; p1 := 1; p2 := 2; p3 := 3
  ordered := by decide

def c8Endpoints0123 : CrossingEndpoints where
  n := 8; p0 := 0; p1 := 1; p2 := 2; p3 := 3
  ordered := by decide

def c9Endpoints0123 : CrossingEndpoints where
  n := 9; p0 := 0; p1 := 1; p2 := 2; p3 := 3
  ordered := by decide

def c10Endpoints0123 : CrossingEndpoints where
  n := 10; p0 := 0; p1 := 1; p2 := 2; p3 := 3
  ordered := by decide

def c11Endpoints0123 : CrossingEndpoints where
  n := 11; p0 := 0; p1 := 1; p2 := 2; p3 := 3
  ordered := by decide

def c12Endpoints0123 : CrossingEndpoints where
  n := 12; p0 := 0; p1 := 1; p2 := 2; p3 := 3
  ordered := by decide

def c13Endpoints0123 : CrossingEndpoints where
  n := 13; p0 := 0; p1 := 1; p2 := 2; p3 := 3
  ordered := by decide

def c14Endpoints0123 : CrossingEndpoints where
  n := 14; p0 := 0; p1 := 1; p2 := 2; p3 := 3
  ordered := by decide

theorem c7Endpoints0123_hop3 : c7Endpoints0123.toArcs.total = 3 := by native_decide
theorem c8Endpoints0123_hop4 : c8Endpoints0123.toArcs.total = 4 := by native_decide
theorem c9Endpoints0123_hop5 : c9Endpoints0123.toArcs.total = 5 := by native_decide
theorem c10Endpoints0123_hop6 : c10Endpoints0123.toArcs.total = 6 := by native_decide
theorem c11Endpoints0123_hop7 : c11Endpoints0123.toArcs.total = 7 := by native_decide
theorem c12Endpoints0123_hop8 : c12Endpoints0123.toArcs.total = 8 := by native_decide
theorem c13Endpoints0123_hop9 : c13Endpoints0123.toArcs.total = 9 := by native_decide
theorem c14Endpoints0123_hop10 : c14Endpoints0123.toArcs.total = 10 := by native_decide

theorem CrossingEndpoints.parametric_goal_hop3 (e : CrossingEndpoints)
    (h : e.toArcs.total = 3) :
    ∃ g : ParametricClosure3Goal, g.arcs = e.toArcs ∧ g.family = .tripleFold := by
  obtain ⟨g, hg⟩ := parametric_goal_from_arcs e.toArcs (by omega) (by omega)
  have hf := g.family_ok
  have ht := CrossingEndpoints.routes_tripleFold e h
  refine ⟨g, hg, ?_⟩
  rw [hg] at hf
  exact Option.some_inj.mp (hf.symm.trans ht)

theorem CrossingEndpoints.parametric_goal_hop4 (e : CrossingEndpoints)
    (h : e.toArcs.total = 4) :
    ∃ g : ParametricClosure3Goal, g.arcs = e.toArcs ∧ g.family = .fourFold := by
  obtain ⟨g, hg⟩ := parametric_goal_from_arcs e.toArcs (by omega) (by omega)
  have hf := g.family_ok
  have ht := CrossingEndpoints.routes_fourFold e h
  refine ⟨g, hg, ?_⟩
  rw [hg] at hf
  exact Option.some_inj.mp (hf.symm.trans ht)

theorem CrossingEndpoints.parametric_goal_hop5 (e : CrossingEndpoints)
    (h : e.toArcs.total = 5) :
    ∃ g : ParametricClosure3Goal, g.arcs = e.toArcs ∧ g.family = .fiveFold := by
  obtain ⟨g, hg⟩ := parametric_goal_from_arcs e.toArcs (by omega) (by omega)
  have hf := g.family_ok
  have ht := CrossingEndpoints.routes_fiveFold e h
  refine ⟨g, hg, ?_⟩
  rw [hg] at hf
  exact Option.some_inj.mp (hf.symm.trans ht)

theorem CrossingEndpoints.parametric_goal_hop6 (e : CrossingEndpoints)
    (h : e.toArcs.total = 6) :
    ∃ g : ParametricClosure3Goal, g.arcs = e.toArcs ∧ g.family = .sixFold := by
  obtain ⟨g, hg⟩ := parametric_goal_from_arcs e.toArcs (by omega) (by omega)
  have hf := g.family_ok
  have ht := CrossingEndpoints.routes_sixFold e h
  refine ⟨g, hg, ?_⟩
  rw [hg] at hf
  exact Option.some_inj.mp (hf.symm.trans ht)

theorem CrossingEndpoints.parametric_goal_hop7 (e : CrossingEndpoints)
    (h : e.toArcs.total = 7) :
    ∃ g : ParametricClosure3Goal, g.arcs = e.toArcs ∧ g.family = .sevenFold := by
  obtain ⟨g, hg⟩ := parametric_goal_from_arcs e.toArcs (by omega) (by omega)
  have hf := g.family_ok
  have ht := CrossingEndpoints.routes_sevenFold e h
  refine ⟨g, hg, ?_⟩
  rw [hg] at hf
  exact Option.some_inj.mp (hf.symm.trans ht)

theorem CrossingEndpoints.parametric_goal_hop8 (e : CrossingEndpoints)
    (h : e.toArcs.total = 8) :
    ∃ g : ParametricClosure3Goal, g.arcs = e.toArcs ∧ g.family = .eightFold := by
  obtain ⟨g, hg⟩ := parametric_goal_from_arcs e.toArcs (by omega) (by omega)
  have hf := g.family_ok
  have ht := CrossingEndpoints.routes_eightFold e h
  refine ⟨g, hg, ?_⟩
  rw [hg] at hf
  exact Option.some_inj.mp (hf.symm.trans ht)

theorem CrossingEndpoints.parametric_goal_hop9 (e : CrossingEndpoints)
    (h : e.toArcs.total = 9) :
    ∃ g : ParametricClosure3Goal, g.arcs = e.toArcs ∧ g.family = .nineFold := by
  obtain ⟨g, hg⟩ := parametric_goal_from_arcs e.toArcs (by omega) (by omega)
  have hf := g.family_ok
  have ht := CrossingEndpoints.routes_nineFold e h
  refine ⟨g, hg, ?_⟩
  rw [hg] at hf
  exact Option.some_inj.mp (hf.symm.trans ht)

theorem CrossingEndpoints.parametric_goal_hop10 (e : CrossingEndpoints)
    (h : e.toArcs.total = 10) :
    ∃ g : ParametricClosure3Goal, g.arcs = e.toArcs ∧ g.family = .tenFold := by
  obtain ⟨g, hg⟩ := parametric_goal_from_arcs e.toArcs (by omega) (by omega)
  have hf := g.family_ok
  have ht := CrossingEndpoints.routes_tenFold e h
  refine ⟨g, hg, ?_⟩
  rw [hg] at hf
  exact Option.some_inj.mp (hf.symm.trans ht)

theorem c7Endpoints_hop3_bundle :
    packFamilyOfHops c7Endpoints0123.toArcs.total = some .tripleFold ∧
      ¬ (CrossingEndpoints.thirdHopElim c7Endpoints0123 c7Endpoints0123_hop3).before.mem [] :=
  let h := CrossingEndpoints.hop3_elim_bundle c7Endpoints0123 c7Endpoints0123_hop3
  ⟨h.1, h.2.2.1⟩

theorem c8Endpoints_hop4_bundle :
    packFamilyOfHops c8Endpoints0123.toArcs.total = some .fourFold ∧
      ¬ (CrossingEndpoints.fourthHopElim c8Endpoints0123 c8Endpoints0123_hop4).before.mem [] :=
  let h := CrossingEndpoints.hop4_elim_bundle c8Endpoints0123 c8Endpoints0123_hop4
  ⟨h.1, h.2.2.1⟩

theorem c8EndpointsEven_hop4_bundle :
    packFamilyOfHops c8EndpointsEven.toArcs.total = some .fourFold ∧
      c8EndpointsEven.toArcs.total = 4 := by
  have ht : c8EndpointsEven.toArcs.total = 4 := by native_decide
  exact ⟨by rw [ht]; rfl, ht⟩

theorem c9Endpoints_hop5_bundle :
    packFamilyOfHops c9Endpoints0123.toArcs.total = some .fiveFold ∧
      ¬ (CrossingEndpoints.fifthHopElim c9Endpoints0123 c9Endpoints0123_hop5).before.mem [] :=
  let h := CrossingEndpoints.hop5_elim_bundle c9Endpoints0123 c9Endpoints0123_hop5
  ⟨h.1, h.2.2.1⟩

theorem c10Endpoints_hop6_bundle :
    packFamilyOfHops c10Endpoints0123.toArcs.total = some .sixFold ∧
      ¬ (CrossingEndpoints.sixthHopElim c10Endpoints0123 c10Endpoints0123_hop6).before.mem [] :=
  let h := CrossingEndpoints.hop6_elim_bundle c10Endpoints0123 c10Endpoints0123_hop6
  ⟨h.1, h.2.2.1⟩

theorem c11Endpoints_hop7_bundle :
    packFamilyOfHops c11Endpoints0123.toArcs.total = some .sevenFold ∧
      ¬ (CrossingEndpoints.seventhHopElim c11Endpoints0123 c11Endpoints0123_hop7).before.mem [] :=
  let h := CrossingEndpoints.hop7_elim_bundle c11Endpoints0123 c11Endpoints0123_hop7
  ⟨h.1, h.2.2.1⟩

theorem c12Endpoints_hop8_bundle :
    packFamilyOfHops c12Endpoints0123.toArcs.total = some .eightFold ∧
      ¬ (CrossingEndpoints.eighthHopElim c12Endpoints0123 c12Endpoints0123_hop8).before.mem [] :=
  let h := CrossingEndpoints.hop8_elim_bundle c12Endpoints0123 c12Endpoints0123_hop8
  ⟨h.1, h.2.2.1⟩

theorem c13Endpoints_hop9_bundle :
    packFamilyOfHops c13Endpoints0123.toArcs.total = some .nineFold ∧
      ¬ (CrossingEndpoints.ninthHopElim c13Endpoints0123 c13Endpoints0123_hop9).before.mem [] :=
  let h := CrossingEndpoints.hop9_elim_bundle c13Endpoints0123 c13Endpoints0123_hop9
  ⟨h.1, h.2.2.1⟩

theorem c14Endpoints_hop10_bundle :
    packFamilyOfHops c14Endpoints0123.toArcs.total = some .tenFold ∧
      ¬ (CrossingEndpoints.tenthHopElim c14Endpoints0123 c14Endpoints0123_hop10).before.mem [] :=
  let h := CrossingEndpoints.hop10_elim_bundle c14Endpoints0123 c14Endpoints0123_hop10
  ⟨h.1, h.2.2.1⟩

/-- Concrete C₅..C₁₄ endpoint bundles cover every pack family hop budget. -/
theorem endpoints0123_all_hop_families :
    packFamilyOfHops c5Endpoints0123.toArcs.total = some .oneFold ∧
      packFamilyOfHops c6Endpoints0123.toArcs.total = some .multiFold ∧
      packFamilyOfHops c7Endpoints0123.toArcs.total = some .tripleFold ∧
      packFamilyOfHops c8Endpoints0123.toArcs.total = some .fourFold ∧
      packFamilyOfHops c9Endpoints0123.toArcs.total = some .fiveFold ∧
      packFamilyOfHops c10Endpoints0123.toArcs.total = some .sixFold ∧
      packFamilyOfHops c11Endpoints0123.toArcs.total = some .sevenFold ∧
      packFamilyOfHops c12Endpoints0123.toArcs.total = some .eightFold ∧
      packFamilyOfHops c13Endpoints0123.toArcs.total = some .nineFold ∧
      packFamilyOfHops c14Endpoints0123.toArcs.total = some .tenFold :=
  ⟨c5Endpoints_hop1_bundle.1, c6Endpoints_hop2_bundle.1, c7Endpoints_hop3_bundle.1,
    c8Endpoints_hop4_bundle.1, c9Endpoints_hop5_bundle.1, c10Endpoints_hop6_bundle.1,
    c11Endpoints_hop7_bundle.1, c12Endpoints_hop8_bundle.1,
    c13Endpoints_hop9_bundle.1, c14Endpoints_hop10_bundle.1⟩

/--
  Parametric routing for the full all-odd mass window:
  every crossing endpoint configuration with `5 ≤ n ≤ 14` meets the
  `ParametricClosure3Goal` checklist (pack route + topology + □-free projection).

  This is still *routing* to OneFold…TenFold, not fresh Closure₃ synthesis.
-/
theorem CrossingEndpoints.parametric_goal_of_mass_window
    (e : CrossingEndpoints) (h5 : 5 ≤ e.n) (h14 : e.n ≤ 14) :
    ∃ g : ParametricClosure3Goal, g.arcs = e.toArcs := by
  have hLo : 1 ≤ e.toArcs.total := by
    rw [CrossingEndpoints.toArcs_total]
    omega
  have hHi : e.toArcs.total ≤ 10 :=
    crossing_hop_budget_le_pack_window e h5 h14
  exact parametric_goal_from_arcs e.toArcs hLo hHi

/-- Same window ⇒ pack family + topology set-eq + □-free G projection. -/
theorem CrossingEndpoints.pack_route_of_mass_window
    (e : CrossingEndpoints) (h5 : 5 ≤ e.n) (h14 : e.n ≤ 14) :
    ∃ f : CrossingPackFamily,
      packFamilyOfHops e.toArcs.total = some f ∧
        packTopologySetEq f = true ∧
        ¬ (packProjection f).gClosure.mem [] := by
  have hLo : 1 ≤ e.toArcs.total := by
    rw [CrossingEndpoints.toArcs_total]
    omega
  have hHi : e.toArcs.total ≤ 10 :=
    crossing_hop_budget_le_pack_window e h5 h14
  exact crossing_pack_route hLo hHi

theorem mass_window_endpoints0123_parametric :
    (∃ g : ParametricClosure3Goal, g.arcs = c5Endpoints0123.toArcs) ∧
      (∃ g : ParametricClosure3Goal, g.arcs = c14Endpoints0123.toArcs) :=
  ⟨CrossingEndpoints.parametric_goal_of_mass_window c5Endpoints0123 (by decide) (by decide),
    CrossingEndpoints.parametric_goal_of_mass_window c14Endpoints0123 (by decide) (by decide)⟩

/--
  Mass-window pack-routed ProjectionInclusion: every endpoints config with
  `5 ≤ n ≤ 14` admits a □-free G→R projection (via OneFold…TenFold).

  Honest: this is pack routing, not a freshly synthesized Closure₃(G_e).
-/
theorem CrossingEndpoints.projectionInclusion_of_mass_window
    (e : CrossingEndpoints) (h5 : 5 ≤ e.n) (h14 : e.n ≤ 14) :
    ∃ P : ProjectionInclusion 3,
      ¬ P.gClosure.mem [] ∧ ¬ P.rClosure.mem [] := by
  obtain ⟨f, _, _, hg⟩ := CrossingEndpoints.pack_route_of_mass_window e h5 h14
  exact ⟨packProjection f, hg, pack_no_empty_residual f⟩

theorem mass_window_c5_c14_projection :
    (∃ P : ProjectionInclusion 3, ¬ P.gClosure.mem [] ∧ ¬ P.rClosure.mem []) ∧
      (∃ P : ProjectionInclusion 3, ¬ P.gClosure.mem [] ∧ ¬ P.rClosure.mem []) :=
  ⟨CrossingEndpoints.projectionInclusion_of_mass_window c5Endpoints0123 (by decide) (by decide),
    CrossingEndpoints.projectionInclusion_of_mass_window c14Endpoints0123 (by decide) (by decide)⟩

def crossingEndpointsElimDoc : String :=
  "papers/FAMILY_PROJECTION_E5.md"

end PNPLab
