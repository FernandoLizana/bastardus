/-
  Fase 4 Lean — noncrossing branch: tw(L(G)) = 3 ⇒ ResolutionWidth = 3.

  Closes the Phase 2 gap where `noncrossing_width_eq_three_when_tw_le_two` assumed
  tw(L(G)) ≤ 2; Python observes tw(L(G)) = 3 on all noncrossing representatives.

  **Hypothesis witnesses** for tw(L(G)) = 3 on smoke graphs; no full tw(L(G)) = 3
  proof ∀n yet.

  External evidence (not Lean proofs):
  - Exact sweep n=5..14: 1870/1870 noncrossing configs tw(L(G)) = 3
    (`reports/CHORD_TREewidth_EXACT_N5_N14.md`, 2870/2870 total).
  - Representative n=5..100: 191/191 noncrossing configs tw(L(G)) = 3
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
  Noncrossing geometry: tw(L(G)) = 3 — verified certificate or experimental Python bound.

  Not a PNPLab proof ∀ noncrossing instances.
  Smoke c8Nested uses proved `HasTreeDecomp` (CertificatesLine).
-/
structure NoncrossingLineGraphTw3 (g : CycleTwoChordGraph) (hnc : ¬ g.chordsCross) where
  tw : LineGraphTwBound (Fin g.n) g.toSimpleGraph 3

/--
  Bundled noncrossing width-3 prediction: literature + C₄ core + tw(L(G)) = 3.
-/
structure NoncrossingWidth3Prediction (g : CycleTwoChordGraph) (hnc : ¬ g.chordsCross) where
  tw3 : NoncrossingLineGraphTw3 g hnc
  core_four : NoncrossingCoreIsFourCycle g hnc
  char : TseitinWidthTreewidthCharacterization (Fin g.n) g.toSimpleGraph 3 3

/--
  Conditional theorem (Fase 4): literature + noncrossing + C₄ core + tw(L(G)) = 3
  ⇒ minimum resolution refutation width = 3 (= max(Δ, tw(L(G))) with Δ = 3).
-/
theorem noncrossing_width_eq_three
    {g : CycleTwoChordGraph} {hnc : ¬ g.chordsCross}
    (pred : NoncrossingWidth3Prediction g hnc)
    (φ : OddMarkingOdd (Fin g.n)) :
    ResolutionWidth (pred.char.tseitin φ) 3 := by
  have h := width_from_treewidth_of_characterization pred.char rfl φ
  simpa [Nat.max_eq_left (by decide : 3 ≤ 3)] using h

/--
  Phase 4 alias: width = 3 when tw(L(G)) = 3 is observed (Python-validated).

  Supersedes the Phase 2 `noncrossing_width_eq_three_when_tw_le_two` path for the
  empirically correct tw(L(G)) = 3 noncrossing branch.
-/
theorem noncrossing_width_eq_three_when_tw_eq_three
    {g : CycleTwoChordGraph} {hnc : ¬ g.chordsCross}
    (pred : NoncrossingWidth3Prediction g hnc)
    (φ : OddMarkingOdd (Fin g.n)) :
    ResolutionWidth (pred.char.tseitin φ) 3 :=
  noncrossing_width_eq_three pred φ

/-! ### Smoke: tw(L(G)) = 3 on c8 nested graph (verified HasTreeDecomp) -/

def c8Nested_noncrossing_lineGraph_tw3 :
    NoncrossingLineGraphTw3 c8NestedGraph c8NestedGraph_not_crossing :=
  { tw := .certified (c8NestedGraph_lineGraph_hasTreeDecomp_three :
      TreewidthCertificate (c8NestedGraph.toSimpleGraph).edgeSet
        (lineGraph c8NestedGraph.toSimpleGraph) 3) }

def c7Nested_noncrossing_lineGraph_tw3 :
    NoncrossingLineGraphTw3 c7NestedGraph c7NestedGraph_not_crossing :=
  { tw := .certified (c7NestedGraph_lineGraph_hasTreeDecomp_3 :
      TreewidthCertificate (c7NestedGraph.toSimpleGraph).edgeSet
        (lineGraph c7NestedGraph.toSimpleGraph) 3) }

def c9Nested_noncrossing_lineGraph_tw3 :
    NoncrossingLineGraphTw3 c9NestedGraph c9NestedGraph_not_crossing :=
  { tw := .certified (c9NestedGraph_lineGraph_hasTreeDecomp_3 :
      TreewidthCertificate (c9NestedGraph.toSimpleGraph).edgeSet
        (lineGraph c9NestedGraph.toSimpleGraph) 3) }

def c10Nested_noncrossing_lineGraph_tw3 :
    NoncrossingLineGraphTw3 c10NestedGraph c10NestedGraph_not_crossing :=
  { tw := .certified (c10NestedGraph_lineGraph_hasTreeDecomp_3 :
      TreewidthCertificate (c10NestedGraph.toSimpleGraph).edgeSet
        (lineGraph c10NestedGraph.toSimpleGraph) 3) }

def noncrossingWidth3Doc : String :=
  "Fase 4 noncrossing: NoncrossingLineGraphTw3 + noncrossing_width_eq_three; " ++
  "c7/c8/c9/c10 nested smokes tw(L(G))=3 verified HasTreeDecomp; " ++
  "closes tw≤2 gap from Phase 2"

def noncrossingWidth3GapDoc : String :=
  "Remaining Fase 5: prove tw(L(G))=3 ∀ noncrossing n; outerplanar tw bounds; " ++
  "universal dichotomy; full Tseitin odd-marking"

end PNPLab.ChordWidth
