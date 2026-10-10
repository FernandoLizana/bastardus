/-
  Fase 5 Lean — main conditional bundle for two-chord resolution width.

  Target unconditional theorem (Phase 5 remaining):

  ```lean
  theorem cycle_two_chords_resolution_width
      {n : Nat} (hn : 5 ≤ n) {g : CycleTwoChordGraph} (hg : g.n = n)
      (hvalid : …) (φ : OddMarkingOdd (Fin n)) :
      (ResolutionWidth (tseitin g φ) 3 ↔ ¬ g.chordsCross)
  ```

  Blocked on: ∀n tw(L(G)) dichotomy, ∀n core classification, full odd-marking
  Tseitin wiring, Mathlib treewidth API.
-/

import PNPLab.ChordWidth.BaseCaseTwoChords.CycleTwoChords.Dichotomy

namespace PNPLab.ChordWidth

open SimpleGraph

/--
  Main Fase 5 conditional bundle (single `CycleTwoChordGraph`, fixed odd φ).

  Given per-instance `TwoChordWidthDichotomy` witnesses:

  - `g.chordsCross` ⇒ minimum resolution refutation width = 4
  - `¬ g.chordsCross` ⇒ minimum resolution refutation width = 3

  Equivalent to the crossing law at this instance once width ∈ {3, 4} is known
  from the tw dichotomy; full biconditional `width = 3 ↔ noncrossing` for a
  unified Tseitin encoding is deferred to the unconditional theorem.
-/
theorem cycle_two_chords_resolution_width_conditional
    {g : CycleTwoChordGraph} (d : TwoChordWidthDichotomy g)
    (φ : OddMarkingOdd (Fin g.n)) :
    (∀ (hc : g.chordsCross),
      ResolutionWidth ((d.crossing_pred hc).char.tseitin φ) 4) ∧
    (∀ (hnc : ¬ g.chordsCross),
      ResolutionWidth ((d.noncrossing_pred hnc).char.tseitin φ) 3) :=
  two_chord_width_dichotomy_conditional d φ

/-- Alias: dichotomy conditional packaged as the main width law at this instance. -/
theorem cycle_two_chords_resolution_width_conditional'
    {g : CycleTwoChordGraph} (d : TwoChordWidthDichotomy g)
    (φ : OddMarkingOdd (Fin g.n)) :
    if hc : g.chordsCross then
      ResolutionWidth ((d.crossing_pred hc).char.tseitin φ) 4
    else
      ResolutionWidth ((d.noncrossing_pred hc).char.tseitin φ) 3 :=
  two_chord_width_dichotomy_conditional_if d φ

/-!
  ### Phase 5 remaining — unconditional ∀n hook

  When the following are available, replace hypothesis bundles with a single proof:

  1. `∀ g valid, g.chordsCross → tw(L(G)) = 4` (real treewidth, not stub witness)
  2. `∀ g valid, ¬ g.chordsCross → tw(L(G)) = 3`
  3. `∀ g valid, CrossingCoreIsK4 g` / `NoncrossingCoreIsFourCycle g` (core iso ∀n)
  4. Unified `TseitinWidthTreewidthCharacterization` for all valid two-chord G
  5. Full odd-marking Tseitin `φ` (not just smoke charge pattern)

  Smoke instances (c5Ofold / c8Nested) already supply branch predictions piecemeal;
  a `TwoChordWidthDichotomy` builder for smoke graphs awaits a shared literature char.
-/

def ChordWidthPhase5Doc : String :=
  twoChordWidthDichotomyDoc ++ " | MainTheorem: " ++
  "cycle_two_chords_resolution_width_conditional (per-instance). " ++
  "Remaining: cycle_two_chords_resolution_width ∀ n ≥ 5; real tw proofs; " ++
  "SimpleGraph.Iso cores; full odd φ Tseitin. Python: 2870/2870 exact + 383/383 rep."

def cycleTwoChordsResolutionWidthGapDoc : String :=
  "Unconditional target: ∀ n ≥ 5, ∀ valid two-chord G on C_n, ∀ odd φ, " ++
  "ResolutionWidth (T(G,φ)) 3 ↔ noncrossing. Gated on Fase 4 tw bounds ∀n."

end PNPLab.ChordWidth
