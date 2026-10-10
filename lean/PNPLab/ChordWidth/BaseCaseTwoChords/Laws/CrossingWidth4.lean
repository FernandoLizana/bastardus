/-
  Fase 4 Lean — crossing branch: tw(L(G)) = 4 ⇒ ResolutionWidth = 4.

  **Hypothesis witnesses** for tw(L(G)) = 4 on smoke graphs; no full tw(L(G)) = 4
  proof ∀n yet (Mathlib lacks `SimpleGraph.treewidth` in v4.32.0).

  External evidence (not Lean proofs):
  - Exact sweep n=5..14: 1000/1000 crossing configs tw(L(G)) = 4
    (`reports/CHORD_TREewidth_EXACT_N5_N14.md`, 2870/2870 total).
  - Representative n=5..100: 192/192 crossing configs tw(L(G)) = 4
    (`reports/CHORD_TREewidth_VERIFICATION.md`, 383/383 total).
-/

import PNPLab.ChordWidth.LiteratureHypothesis
import PNPLab.ChordWidth.BaseCaseTwoChords.TwoChordCore
import PNPLab.ChordWidth.Treewidth
import PNPLab.ChordWidth.TreeDecomp.CertificatesLine
import PNPLab.ChordWidth.TreeDecomp.CertificatesLineSmokes

namespace PNPLab.ChordWidth

open SmokeLineGraphCert

open SimpleGraph

/--
  Crossing geometry: tw(L(G)) = 4 — verified certificate or experimental Python bound.

  Not a PNPLab proof that tw(L(G)) = 4 for all crossing instances.
  Smoke c5Ofold uses proved `HasTreeDecomp` (CertificatesLine).
-/
structure CrossingLineGraphTw4 (g : CycleTwoChordGraph) (hc : g.chordsCross) where
  tw : LineGraphTwBound (Fin g.n) g.toSimpleGraph 4

/--
  Bundled crossing width-4 prediction: literature + K₄ core + tw(L(G)) = 4.
-/
structure CrossingWidth4Prediction (g : CycleTwoChordGraph) (hc : g.chordsCross) where
  tw4 : CrossingLineGraphTw4 g hc
  core_k4 : CrossingCoreIsK4 g hc
  char : TseitinWidthTreewidthCharacterization (Fin g.n) g.toSimpleGraph 3 4

/--
  Conditional theorem (Fase 4): literature + crossing + K₄ core + tw(L(G)) = 4
  ⇒ minimum resolution refutation width = 4 (= max(Δ, tw(L(G))) with Δ = 3).
-/
theorem crossing_width_eq_four
    {g : CycleTwoChordGraph} {hc : g.chordsCross}
    (pred : CrossingWidth4Prediction g hc)
    (φ : OddMarkingOdd (Fin g.n)) :
    ResolutionWidth (pred.char.tseitin φ) 4 := by
  have h := width_from_treewidth_of_characterization pred.char rfl φ
  simpa [Nat.max_eq_right (by decide : 3 ≤ 4)] using h

/-! ### Smoke: tw(L(G)) = 4 on c5 crossing graph (verified HasTreeDecomp) -/

def c5Ofold_crossing_lineGraph_tw4 :
    CrossingLineGraphTw4 c5OfoldGraph c5OfoldGraph_chordsCross :=
  { tw := .certified (c5OfoldGraph_lineGraph_hasTreeDecomp_four :
      TreewidthCertificate (c5OfoldGraph.toSimpleGraph).edgeSet
        (lineGraph c5OfoldGraph.toSimpleGraph) 4) }

def c6Crossing_crossing_lineGraph_tw4 :
    CrossingLineGraphTw4 c6CrossingGraph c6CrossingGraph_chordsCross :=
  { tw := .certified (c6CrossingGraph_lineGraph_hasTreeDecomp_4 :
      TreewidthCertificate (c6CrossingGraph.toSimpleGraph).edgeSet
        (lineGraph c6CrossingGraph.toSimpleGraph) 4) }

def c7Crossing_crossing_lineGraph_tw4 :
    CrossingLineGraphTw4 c7CrossingGraph c7CrossingGraph_chordsCross :=
  { tw := .certified (c7CrossingGraph_lineGraph_hasTreeDecomp_4 :
      TreewidthCertificate (c7CrossingGraph.toSimpleGraph).edgeSet
        (lineGraph c7CrossingGraph.toSimpleGraph) 4) }

def c8Crossing_crossing_lineGraph_tw4 :
    CrossingLineGraphTw4 c8CrossingGraph c8CrossingGraph_chordsCross :=
  { tw := .certified (c8CrossingGraph_lineGraph_hasTreeDecomp_4 :
      TreewidthCertificate (c8CrossingGraph.toSimpleGraph).edgeSet
        (lineGraph c8CrossingGraph.toSimpleGraph) 4) }

def c9Crossing_crossing_lineGraph_tw4 :
    CrossingLineGraphTw4 c9CrossingGraph c9CrossingGraph_chordsCross :=
  { tw := .certified (c9CrossingGraph_lineGraph_hasTreeDecomp_4 :
      TreewidthCertificate (c9CrossingGraph.toSimpleGraph).edgeSet
        (lineGraph c9CrossingGraph.toSimpleGraph) 4) }

def c10Crossing_crossing_lineGraph_tw4 :
    CrossingLineGraphTw4 c10CrossingGraph c10CrossingGraph_chordsCross :=
  { tw := .certified (c10CrossingGraph_lineGraph_hasTreeDecomp_4 :
      TreewidthCertificate (c10CrossingGraph.toSimpleGraph).edgeSet
        (lineGraph c10CrossingGraph.toSimpleGraph) 4) }

def crossingWidth4Doc : String :=
  "Fase 4 crossing: CrossingLineGraphTw4 + crossing_width_eq_four; " ++
  "c5/c6/c7/c8/c9/c10 crossing smokes tw(L(G))=4 verified HasTreeDecomp; " ++
  "Python 2870/2870 exact + 383/383 representative"

def crossingWidth4GapDoc : String :=
  "Remaining Fase 5: prove tw(L(G))=4 ∀ crossing n; universal dichotomy; full Tseitin odd-marking"

end PNPLab.ChordWidth
