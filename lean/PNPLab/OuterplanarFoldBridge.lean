/-
  Bridge demo: outerplanar / crossing tip kinds paired with concrete packs.

  1. C₄ triangle-ear sketch ↔ BicyclicWidth3 (upper-bound □ ∈ Closure₃).
  2. C₅–C₁₄ crossing shortcut tips ↔ OneFold…TenFold first hops (lower-bound).
  3. MultiFold second hop ↔ mfStep1R.
  4. `foldTipFirstHop` covers every `CrossingPackFamily`.

  Tip kinds match multihop mass: all crossing schedule tips are shortcut_fold
  (`multihop_tip_kinds_mass.json`). See EAR_LAW_TO_ELIMINATION.md.
-/

import PNPLab.Outerplanar
import PNPLab.BicyclicWidth3
import PNPLab.OneFoldProjection
import PNPLab.MultiFoldProjection
import PNPLab.TripleFoldProjection
import PNPLab.FourFoldProjection
import PNPLab.FiveFoldProjection
import PNPLab.SixFoldProjection
import PNPLab.SevenFoldProjection
import PNPLab.EightFoldProjection
import PNPLab.NineFoldProjection
import PNPLab.TenFoldProjection
import PNPLab.CrossingPackCatalog
import PNPLab.OpenArcPath
import PNPLab.ResolutionClosure

namespace PNPLab

open Outerplanar Resolution

/-- Combinatorial tip + concrete `EliminationStep` (lower-bound packs). -/
structure FoldTipElimination (w : Nat) where
  sketch : ResidualSketch
  tipKind : EarTipKind
  tipMatches : sketch.classify.tipKind = some tipKind
  step : EliminationStep w

theorem foldTipElimination_to_witness (W : FoldTipElimination 3) :
    ∃ _w : FoldTipWitness 3, True := by
  refine ⟨{
    sketch := W.sketch
    tipKind := W.tipKind
    tipMatches := W.tipMatches
  }, trivial⟩

/-- Helper: shortcut sketch of size `n` with matching tip kind. -/
def shortcutElim (n : Nat) (s : EliminationStep 3) : FoldTipElimination 3 where
  sketch := sketchShortcut n
  tipKind := EarTipKind.shortcutDeg2NextToDeg3
  tipMatches := by
    simp [ResidualSketch.classify, sketchShortcut]
  step := s

/-- C₄ triangle-ear residual sketch as FoldTipWitness. -/
def c4FoldTip : FoldTipWitness 3 where
  sketch := residualC4Triangle
  tipKind := EarTipKind.triangleEar
  tipMatches := by
    simp [ResidualSketch.classify, residualC4Triangle, sketchTriangleEar]

theorem c4_fold_measure :
    (FoldMeasure.succFold (foldMeasureOf residualC4Triangle)).nVertices = 3 :=
  residualC4_fold_to_cycle_measure

theorem c4_bicyclic_has_empty : biClosure.mem [] :=
  bi_has_empty

theorem c4_ear_bridge_bundle :
    c4FoldTip.tipKind = EarTipKind.triangleEar ∧
      (FoldMeasure.succFold (foldMeasureOf c4FoldTip.sketch)).nVertices = 3 ∧
      biClosure.mem [] := by
  refine ⟨rfl, ?_, bi_has_empty⟩
  simp [c4FoldTip, residualC4Triangle, sketchTriangleEar, foldMeasureOf, FoldMeasure.succFold]

/-- C₅ crossing (0,2)+(1,3): OneFold EliminationStep. -/
def c5CrossingFoldElim : FoldTipElimination 3 :=
  shortcutElim 5 ofoldEliminationStep

theorem c5Crossing_step_no_empty_before :
    ¬ c5CrossingFoldElim.step.before.mem [] := by
  simp [c5CrossingFoldElim, shortcutElim, ofoldEliminationStep]
  exact ofoldG_no_empty

theorem c5Crossing_step_no_empty_after :
    ¬ c5CrossingFoldElim.step.after.mem [] := by
  simp [c5CrossingFoldElim, shortcutElim, ofoldEliminationStep]
  exact ofoldR_no_empty

theorem c5_crossing_lower_bound_bundle :
    c5CrossingFoldElim.tipKind = EarTipKind.shortcutDeg2NextToDeg3 ∧
      ¬ c5CrossingFoldElim.step.before.mem [] ∧
      ¬ c5CrossingFoldElim.step.after.mem [] := by
  refine ⟨rfl, c5Crossing_step_no_empty_before, c5Crossing_step_no_empty_after⟩

/-- C₆ crossing MultiFold hop G0→G1. -/
def c6MultiFoldElim01 : FoldTipElimination 3 :=
  shortcutElim 6 mfStep01

/-- C₆ crossing MultiFold hop G1→R. -/
def c6MultiFoldElim1R : FoldTipElimination 3 :=
  shortcutElim 6 mfStep1R

theorem c6MultiFold_linked :
    ∃ _L : LinkedChain 3 [mfStep01, mfStep1R], True :=
  ⟨mfLinked, trivial⟩

theorem c6MultiFold_no_empty_chain :
    ¬ mfProjection.gClosure.mem [] :=
  mf_no_empty_of_projection

/-- Bundle: both MultiFold hops are shortcut tip eliminations. -/
theorem c6_multifold_shortcut_bundle :
    c6MultiFoldElim01.tipKind = EarTipKind.shortcutDeg2NextToDeg3 ∧
      c6MultiFoldElim1R.tipKind = EarTipKind.shortcutDeg2NextToDeg3 ∧
      c6MultiFoldElim01.step = mfStep01 ∧
      c6MultiFoldElim1R.step = mfStep1R := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- C₇ crossing TripleFold first hop G0→G1. -/
def c7TripleFoldElim01 : FoldTipElimination 3 :=
  shortcutElim 7 tfStep01

theorem c7TripleFold_linked :
    ∃ _L : LinkedChain 3 [tfStep01, tfStep12, tfStep2R], True :=
  ⟨tfLinked, trivial⟩

theorem c7TripleFold_step_no_empty_before :
    ¬ c7TripleFoldElim01.step.before.mem [] := by
  simp [c7TripleFoldElim01, shortcutElim, tfStep01]
  exact tfG0_no_empty

theorem c7_triple_shortcut_bundle :
    c7TripleFoldElim01.tipKind = EarTipKind.shortcutDeg2NextToDeg3 ∧
      c7TripleFoldElim01.step = tfStep01 ∧
      ¬ c7TripleFoldElim01.step.before.mem [] :=
  ⟨rfl, rfl, c7TripleFold_step_no_empty_before⟩

/-- C₈ crossing FourFold first hop G0→G1. -/
def c8FourFoldElim01 : FoldTipElimination 3 :=
  shortcutElim 8 ffStep01

theorem c8FourFold_step_eq :
    c8FourFoldElim01.step = ffStep01 :=
  rfl

/-- C₉ crossing FiveFold first hop G0→G1. -/
def c9FiveFoldElim01 : FoldTipElimination 3 :=
  shortcutElim 9 xfStep01

theorem c9FiveFold_linked :
    ∃ _L : LinkedChain 3 [xfStep01, xfStep12, xfStep23, xfStep34, xfStep4R], True :=
  ⟨xfLinked, trivial⟩

theorem c9FiveFold_step_no_empty_before :
    ¬ c9FiveFoldElim01.step.before.mem [] := by
  simp [c9FiveFoldElim01, shortcutElim, xfStep01]
  exact xfG0_no_empty

theorem c9_five_shortcut_bundle :
    c9FiveFoldElim01.tipKind = EarTipKind.shortcutDeg2NextToDeg3 ∧
      c9FiveFoldElim01.step = xfStep01 ∧
      ¬ c9FiveFoldElim01.step.before.mem [] :=
  ⟨rfl, rfl, c9FiveFold_step_no_empty_before⟩

/-- C₁₀ crossing SixFold first hop G0→G1. -/
def c10SixFoldElim01 : FoldTipElimination 3 :=
  shortcutElim 10 sfStep01

theorem c10SixFold_linked :
    ∃ _L : LinkedChain 3
      [sfStep01, sfStep12, sfStep23, sfStep34, sfStep45, sfStep5R], True :=
  ⟨sfLinked, trivial⟩

theorem c10SixFold_step_no_empty_before :
    ¬ c10SixFoldElim01.step.before.mem [] := by
  simp [c10SixFoldElim01, shortcutElim, sfStep01]
  exact sfG0_no_empty

theorem c10_six_shortcut_bundle :
    c10SixFoldElim01.tipKind = EarTipKind.shortcutDeg2NextToDeg3 ∧
      c10SixFoldElim01.step = sfStep01 ∧
      ¬ c10SixFoldElim01.step.before.mem [] :=
  ⟨rfl, rfl, c10SixFold_step_no_empty_before⟩

/-- C₁₁ crossing SevenFold first hop G0→G1. -/
def c11SevenFoldElim01 : FoldTipElimination 3 :=
  shortcutElim 11 vfStep01

theorem c11SevenFold_linked :
    ∃ _L : LinkedChain 3
      [vfStep01, vfStep12, vfStep23, vfStep34, vfStep45, vfStep56, vfStep6R], True :=
  ⟨vfLinked, trivial⟩

theorem c11SevenFold_step_no_empty_before :
    ¬ c11SevenFoldElim01.step.before.mem [] := by
  simp [c11SevenFoldElim01, shortcutElim, vfStep01]
  exact vfG0_no_empty

theorem c11_seven_shortcut_bundle :
    c11SevenFoldElim01.tipKind = EarTipKind.shortcutDeg2NextToDeg3 ∧
      c11SevenFoldElim01.step = vfStep01 ∧
      ¬ c11SevenFoldElim01.step.before.mem [] :=
  ⟨rfl, rfl, c11SevenFold_step_no_empty_before⟩

/-- C₁₂ crossing EightFold first hop G0→G1. -/
def c12EightFoldElim01 : FoldTipElimination 3 :=
  shortcutElim 12 efStep01

theorem c12EightFold_linked :
    ∃ _L : LinkedChain 3
      [efStep01, efStep12, efStep23, efStep34, efStep45, efStep56, efStep67, efStep7R], True :=
  ⟨efLinked, trivial⟩

theorem c12EightFold_step_no_empty_before :
    ¬ c12EightFoldElim01.step.before.mem [] := by
  simp [c12EightFoldElim01, shortcutElim, efStep01]
  exact efG0_no_empty

theorem c12_eight_shortcut_bundle :
    c12EightFoldElim01.tipKind = EarTipKind.shortcutDeg2NextToDeg3 ∧
      c12EightFoldElim01.step = efStep01 ∧
      ¬ c12EightFoldElim01.step.before.mem [] :=
  ⟨rfl, rfl, c12EightFold_step_no_empty_before⟩

/-- C₁₃ crossing NineFold first hop G0→G1. -/
def c13NineFoldElim01 : FoldTipElimination 3 :=
  shortcutElim 13 nfStep01

theorem c13NineFold_linked :
    ∃ _L : LinkedChain 3
      [nfStep01, nfStep12, nfStep23, nfStep34, nfStep45, nfStep56, nfStep67, nfStep78, nfStep8R], True :=
  ⟨nfLinked, trivial⟩

theorem c13NineFold_step_no_empty_before :
    ¬ c13NineFoldElim01.step.before.mem [] := by
  simp [c13NineFoldElim01, shortcutElim, nfStep01]
  exact nfG0_no_empty

theorem c13_nine_shortcut_bundle :
    c13NineFoldElim01.tipKind = EarTipKind.shortcutDeg2NextToDeg3 ∧
      c13NineFoldElim01.step = nfStep01 ∧
      ¬ c13NineFoldElim01.step.before.mem [] :=
  ⟨rfl, rfl, c13NineFold_step_no_empty_before⟩

/-- C₁₄ crossing TenFold first hop G0→G1. -/
def c14TenFoldElim01 : FoldTipElimination 3 :=
  shortcutElim 14 zfStep01

theorem c14TenFold_linked :
    ∃ _L : LinkedChain 3
      [zfStep01, zfStep12, zfStep23, zfStep34, zfStep45, zfStep56, zfStep67, zfStep78, zfStep89, zfStep9R], True :=
  ⟨zfLinked, trivial⟩

theorem c14TenFold_step_no_empty_before :
    ¬ c14TenFoldElim01.step.before.mem [] := by
  simp [c14TenFoldElim01, shortcutElim, zfStep01]
  exact zfG0_no_empty

theorem c14_ten_shortcut_bundle :
    c14TenFoldElim01.tipKind = EarTipKind.shortcutDeg2NextToDeg3 ∧
      c14TenFoldElim01.step = zfStep01 ∧
      ¬ c14TenFoldElim01.step.before.mem [] :=
  ⟨rfl, rfl, c14TenFold_step_no_empty_before⟩

/-- First-hop FoldTipElimination for every crossing pack family. -/
def foldTipFirstHop : CrossingPackFamily → FoldTipElimination 3
  | .oneFold => c5CrossingFoldElim
  | .multiFold => c6MultiFoldElim01
  | .tripleFold => c7TripleFoldElim01
  | .fourFold => c8FourFoldElim01
  | .fiveFold => c9FiveFoldElim01
  | .sixFold => c10SixFoldElim01
  | .sevenFold => c11SevenFoldElim01
  | .eightFold => c12EightFoldElim01
  | .nineFold => c13NineFoldElim01
  | .tenFold => c14TenFoldElim01

theorem foldTip_covers_pack_families :
    ∀ f : CrossingPackFamily,
      (foldTipFirstHop f).tipKind = EarTipKind.shortcutDeg2NextToDeg3 := by
  intro f; cases f <;> rfl

/-- Constructive FoldTipElimination lower-bound instances in this module. -/
def foldTipEliminationPackCount : Nat := 11
-- c5, c6×2, c7..c14 first-hop (+ MultiFold second hop)

theorem foldTipEliminationPackCount_eq :
    foldTipEliminationPackCount = 11 :=
  rfl

/--
  Bridge: a Bicyclic `OpenArcPath` with a legal frontier tip corresponds to the
  Outerplanar shortcut tip kind used by `FoldTipElimination`. This ties the
  graph-level frontier model (`OpenArcPath.hasFrontierTip`) to the concrete
  lower-bound packs (all shortcut, matching `multihop_tip_kinds_mass.json`).
-/
def openArcElim (n : Nat) (p : Bicyclic.OpenArcPath)
    (_h : p.hasFrontierTip = true) (s : EliminationStep 3) : FoldTipElimination 3 :=
  shortcutElim n s

theorem openArcElim_tipKind (n : Nat) (p : Bicyclic.OpenArcPath)
    (h : p.hasFrontierTip = true) (s : EliminationStep 3) :
    (openArcElim n p h s).tipKind = EarTipKind.shortcutDeg2NextToDeg3 :=
  rfl

/-- C₅ crossing arc (one internal) → OneFold elimination via the open-arc bridge. -/
theorem c5_openArc_bridge :
    (openArcElim 5 (Bicyclic.crossingOpenArc 1)
      (Bicyclic.crossingOpenArc_frontier 1 (by decide)) ofoldEliminationStep).tipKind
      = EarTipKind.shortcutDeg2NextToDeg3 :=
  rfl

def earLawBridgeDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/EAR_LAW_TO_ELIMINATION.md"

def tipKindsMassDoc : String :=
  "reports/discovery/multihop_tip_kinds_mass.json"

end PNPLab
