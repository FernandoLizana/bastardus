/-
  Fase 5 Lean — per-instance two-chord width dichotomy (conditional).

  Bundles crossing (width = 4) and noncrossing (width = 3) branches from Fase 4
  Laws modules. **Requires explicit hypothesis witnesses per graph instance** —
  not a ∀n universal theorem yet.
-/

import PNPLab.ChordWidth.BaseCaseTwoChords.Laws.CrossingWidth4
import PNPLab.ChordWidth.BaseCaseTwoChords.Laws.NoncrossingWidth3

namespace PNPLab.ChordWidth

open SimpleGraph

/--
  Per-instance dichotomy bundle (Fase 5 conditional).

  Fields supply literature characterization + tw(L(G)) witnesses + core
  classification for **this** graph `g` on both branches:

  - crossing: `CrossingWidth4Prediction` (tw = 4, K₄ core)
  - noncrossing: `NoncrossingWidth3Prediction` (tw = 3, C₄ core)

  **Honest scope:** hypothesis witnesses per instance; universal
  `∀ n ≥ 5, ∀ valid G, …` is Phase 5 remaining work (see `MainTheorem.lean`).
-/
structure TwoChordWidthDichotomy (g : CycleTwoChordGraph) where
  crossing_pred : ∀ (hc : g.chordsCross), CrossingWidth4Prediction g hc
  noncrossing_pred : ∀ (hnc : ¬ g.chordsCross), NoncrossingWidth3Prediction g hnc

/-- Crossing branch: literature + tw = 4 + K₄ core ⇒ resolution width = 4. -/
theorem crossing_implies_width_four
    {g : CycleTwoChordGraph} {hc : g.chordsCross}
    (pred : CrossingWidth4Prediction g hc)
    (φ : OddMarkingOdd (Fin g.n)) :
    ResolutionWidth (pred.char.tseitin φ) 4 :=
  crossing_width_eq_four pred φ

/-- Noncrossing branch: literature + tw = 3 + C₄ core ⇒ resolution width = 3. -/
theorem noncrossing_implies_width_three
    {g : CycleTwoChordGraph} {hnc : ¬ g.chordsCross}
    (pred : NoncrossingWidth3Prediction g hnc)
    (φ : OddMarkingOdd (Fin g.n)) :
    ResolutionWidth (pred.char.tseitin φ) 3 :=
  noncrossing_width_eq_three pred φ

/--
  Conditional dichotomy at fixed odd marking φ: crossing ⇒ width 4, else width 3.

  Uses the branch-appropriate literature `char.tseitin` from the bundled
  predictions (not a single unified characterization unless both branches share
  the same `tseitin` definition — Phase 5 remaining).
-/
theorem two_chord_width_dichotomy_conditional
    {g : CycleTwoChordGraph} (d : TwoChordWidthDichotomy g)
    (φ : OddMarkingOdd (Fin g.n)) :
    (∀ (hc : g.chordsCross),
      ResolutionWidth ((d.crossing_pred hc).char.tseitin φ) 4) ∧
    (∀ (hnc : ¬ g.chordsCross),
      ResolutionWidth ((d.noncrossing_pred hnc).char.tseitin φ) 3) :=
  ⟨fun hc => crossing_implies_width_four (d.crossing_pred hc) φ,
   fun hnc => noncrossing_implies_width_three (d.noncrossing_pred hnc) φ⟩

instance (g : CycleTwoChordGraph) : Decidable g.chordsCross := by
  unfold CycleTwoChordGraph.chordsCross
  infer_instance

/--
  Same dichotomy in `if`-then-else form (requires `Decidable g.chordsCross`).
-/
theorem two_chord_width_dichotomy_conditional_if
    {g : CycleTwoChordGraph} (d : TwoChordWidthDichotomy g)
    (φ : OddMarkingOdd (Fin g.n)) :
    if hc : g.chordsCross then
      ResolutionWidth ((d.crossing_pred hc).char.tseitin φ) 4
    else
      ResolutionWidth ((d.noncrossing_pred hc).char.tseitin φ) 3 := by
  split_ifs with hc
  · exact crossing_implies_width_four (d.crossing_pred hc) φ
  · exact noncrossing_implies_width_three (d.noncrossing_pred hc) φ

def twoChordWidthDichotomyDoc : String :=
  "Fase 5 conditional: TwoChordWidthDichotomy bundles crossing/noncrossing " ++
  "predictions; two_chord_width_dichotomy_conditional. Per-instance tw witnesses."

def twoChordWidthDichotomyGapDoc : String :=
  "Remaining: prove tw(L(G))=4/3 ∀ valid instances; universal ∀n core iso; " ++
  "single literature char; cycle_two_chords_resolution_width (unconditional)."

end PNPLab.ChordWidth
