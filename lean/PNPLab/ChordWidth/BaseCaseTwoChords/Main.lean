/-
  Two-chord base case (k = 2): finite-structural width 3/4 pipeline.

  Moved from ChordWidth root; proofs preserved. Not an asymptotic P≠NP result.
-/

import PNPLab.ChordWidth.BaseCaseTwoChords.CycleTwoChords
import PNPLab.ChordWidth.BaseCaseTwoChords.ArcLengths
import PNPLab.ChordWidth.BaseCaseTwoChords.EdgeIndexing
import PNPLab.ChordWidth.BaseCaseTwoChords.NoncrossingPathDecomp
import PNPLab.ChordWidth.BaseCaseTwoChords.GenericDecomp
import PNPLab.ChordWidth.BaseCaseTwoChords.DegreeBounds
import PNPLab.ChordWidth.BaseCaseTwoChords.TseitinEncoding
import PNPLab.ChordWidth.BaseCaseTwoChords.DegreeTwoSuppression
import PNPLab.ChordWidth.BaseCaseTwoChords.TwoChordCore
import PNPLab.ChordWidth.BaseCaseTwoChords.Laws.CrossingWidth4
import PNPLab.ChordWidth.BaseCaseTwoChords.Laws.NoncrossingWidth3
import PNPLab.ChordWidth.BaseCaseTwoChords.CycleTwoChords.MainTheorem
import PNPLab.ChordWidth.BaseCaseTwoChords.TwoChordLink

namespace PNPLab.ChordWidth

open SimpleGraph

/--
  Conditional context: literature hypothesis at Δ = 3 and nominal tw(L(G)) = k.

  `k` is a parameter; tw certificate is optional (`ExperimentalTreewidthBound` in Laws/).
-/
structure TwoChordWidthContext (g : CycleTwoChordGraph) (k : Nat) where
  maxDegree3 : g.maxDegree_eq_three
  char : TseitinWidthTreewidthCharacterization (Fin g.n) g.toSimpleGraph 3 k

theorem two_chord_width_from_characterization
    {g : CycleTwoChordGraph} {k : Nat}
    (ctx : TwoChordWidthContext g k)
    (φ : OddMarkingOdd (Fin g.n)) :
    ResolutionWidth (ctx.char.tseitin φ) (max 3 k) :=
  width_from_treewidth_of_characterization (G := g.toSimpleGraph) ctx.char rfl φ

theorem two_chord_width_from_characterization_of_delta3
    {g : CycleTwoChordGraph} {k : Nat}
    (_hΔ : g.isDelta3Admissible)
    (ctx : TwoChordWidthContext g k)
    (φ : OddMarkingOdd (Fin g.n)) :
    ResolutionWidth (ctx.char.tseitin φ) (max 3 k) :=
  two_chord_width_from_characterization ctx φ

def TwoChordWidthContext.ofSmokeUnification
    {g : CycleTwoChordGraph} {k : Nat}
    (u : TwoChordSmokeTseitinUnification g)
    (width : ∀ φ : OddMarkingOdd (Fin g.n), ResolutionWidth (u.tseitin φ) (max 3 k)) :
    TwoChordWidthContext g k where
  maxDegree3 := g.maxDegree_eq_three_of_ordered
  char := {
    tseitin := u.tseitin
    width_eq := width
  }

structure CrossingWidthPrediction (g : CycleTwoChordGraph) (k : Nat)
    (hc : g.chordsCross) extends TwoChordWidthContext g k where
  core_k4 : CrossingCoreIsK4 g hc
  tw_exp : CrossingLineGraphTw4 g hc

structure NoncrossingWidthPrediction (g : CycleTwoChordGraph) (k : Nat)
    (hnc : ¬ g.chordsCross) extends TwoChordWidthContext g k where
  core_four : NoncrossingCoreIsFourCycle g hnc
  tw_exp : NoncrossingLineGraphTw3 g hnc
  tw_small : k ≤ 3

theorem crossing_width_prediction_value
    {g : CycleTwoChordGraph} {k : Nat} {hc : g.chordsCross}
    (pred : CrossingWidthPrediction g k hc)
    (φ : OddMarkingOdd (Fin g.n)) :
    ResolutionWidth (pred.char.tseitin φ) (max 3 k) :=
  two_chord_width_from_characterization pred.toTwoChordWidthContext φ

theorem noncrossing_width_prediction_value
    {g : CycleTwoChordGraph} {k : Nat} {hnc : ¬ g.chordsCross}
    (pred : NoncrossingWidthPrediction g k hnc)
    (φ : OddMarkingOdd (Fin g.n)) :
    ResolutionWidth (pred.char.tseitin φ) (max 3 k) :=
  two_chord_width_from_characterization pred.toTwoChordWidthContext φ

theorem noncrossing_width_eq_three_when_tw_le_three
    {g : CycleTwoChordGraph} {k : Nat} {hnc : ¬ g.chordsCross}
    (pred : NoncrossingWidthPrediction g k hnc)
    (φ : OddMarkingOdd (Fin g.n)) :
    ResolutionWidth (pred.char.tseitin φ) 3 := by
  have hk : max 3 k = 3 := Nat.max_eq_left pred.tw_small
  simpa [hk] using noncrossing_width_prediction_value pred φ

def baseCaseTwoChordsDoc : String :=
  "Caso base k=2: ancho 3/4 condicional (literatura + núcleo K₄/C₄). " ++
  "tw(L(G)): c5/c6/c7/c8/c9/c10 crossing + c7/c8/c9/c10 nested verified HasTreeDecomp."

end PNPLab.ChordWidth
