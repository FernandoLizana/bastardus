# ChordWidth Lean — Status (Fase 1–5 Lean MVP)

**Updated:** 2026-08-04 (AI universal track + ArcLengths)  
**Integration summary:** [CHORDWIDTH_INTEGRATION_SUMMARY.md](CHORDWIDTH_INTEGRATION_SUMMARY.md)  
**Build target:** `lake build PNPLab.ChordWidth.Main`  
**Last green build:** **1278 jobs** (2026-08-06: `mkGenericDecompFinTransport`, `genericDecompNodeCount_eq_card` PROVED)
**AI audit:** [CHORDWIDTH_AI_BASELINE_AUDIT.md](CHORDWIDTH_AI_BASELINE_AUDIT.md) · [CHORDWIDTH_AI_FINAL_REPORT.md](CHORDWIDTH_AI_FINAL_REPORT.md)
**Audit:** [CROSSING_LAW_SOUNDNESS_AUDIT.md](CROSSING_LAW_SOUNDNESS_AUDIT.md)  
**Paper:** [CHORD_DIAGRAM_TSEITIN_WIDTH.md](../papers/CHORD_DIAGRAM_TSEITIN_WIDTH.md) (§7–8 expanded)  
**Community:** [COMMUNITY_QUESTION_DRAFT.md](COMMUNITY_QUESTION_DRAFT.md) · [Zulip copy-paste](ZULIP_MESSAGE_READY.txt) · [Zulip guide](ZULIP_POSTING_GUIDE.md) · [Mathlib tw status](MATHLIB_TW_STATUS.md)

---

## Module layout

| File | Role |
|------|------|
| `LiteratureHypothesis.lean` | `TseitinWidthTreewidthCharacterization` (literature hypothesis) + conditional theorems |
| `CycleTwoChords.lean` | `CycleTwoChordGraph`, crossing/noncrossing, smoke c5–c10, transport lemmas |
| `DegreeBounds.lean` | **`isDelta3Admissible`** (= Python filter); `isNondegenerate`, `crossing_isNondegenerate` **proved**; **`toSimpleGraph_maxDegree_le` ∀g**, **`isNondegenerate → realMaxDegreeThree`**, **`crossing_isDelta3Admissible`**; `SimpleGraph/DegreeSup.lean` (`neighborFinset_sup`, `degree_sup_le_add`) |
| `TseitinEncoding.lean` | **Fase 5:** `oddChargeFromMarking`, `tseitinFromMarking`, `tseitinAxiomsFromMarking` (noncrossing φ); default φ smoke = legacy axioms; crossing branch still fixed encoder |
| `LineGraph.lean` | Mathlib `SimpleGraph.lineGraph` alias |
| `Treewidth.lean` | `TreewidthWitness` + `EliminationOrder` scaffolding; K₄/C₄ smoke; `LineGraphTreewidthEliminationWitness` |
| `DegreeTwoSuppression.lean` | Branch vertices, `suppressDegreeTwoPaths`, `canonicalSuppressedCore`, graph-transport lemmas |
| `TwoChordCore.lean` | Structural `SuppressedCore.isK4` / `isFourCycle`, smoke + instance witnesses |
| `Laws/CrossingWidth4.lean` | **Fase 4:** `CrossingLineGraphTw4`, `crossing_width_eq_four`, c5 smoke tw=4 |
| `Laws/NoncrossingWidth3.lean` | **Fase 4:** `NoncrossingLineGraphTw3`, `noncrossing_width_eq_three_when_tw_eq_three`, c8 smoke tw=3 |
| `CycleTwoChords/Dichotomy.lean` | **Fase 5:** `TwoChordWidthDichotomy`, `crossing_implies_width_four`, `noncrossing_implies_width_three`, `two_chord_width_dichotomy_conditional` |
| `CycleTwoChords/MainTheorem.lean` | **Fase 5:** `cycle_two_chords_resolution_width_conditional`, `ChordWidthPhase5Doc`, ∀n hook comments |
| `Main.lean` | Bundle + `TwoChordWidthContext.ofSmokeUnification` + `two_chord_width_from_characterization_of_delta3` + phase docs |

**Not imported by** `PNPLab.lean` — isolated build to avoid touching 461-case tree.

---

## Phase 5 — proven (conditional per-instance)

### Width dichotomy bundle (`CycleTwoChords/Dichotomy.lean`)

| Item | Status |
|------|--------|
| `TwoChordWidthDichotomy` | Structure bundling crossing + noncrossing Fase 4 predictions per graph |
| `crossing_implies_width_four` | Alias of `crossing_width_eq_four` on bundled prediction |
| `noncrossing_implies_width_three` | Alias of `noncrossing_width_eq_three` on bundled prediction |
| `two_chord_width_dichotomy_conditional` | Crossing ⇒ width 4, noncrossing ⇒ width 3 (fixed φ, per instance) |
| `two_chord_width_dichotomy_conditional_if` | Same in `if hc : g.chordsCross then … else …` form |
| `Decidable g.chordsCross` | Instance for dichotomy case split |

**Honest scope:** requires explicit tw + literature + core witnesses **per graph instance**; not `∀ n` yet.

### Tseitin encoding bridge (`TseitinEncoding.lean`)

| Item | Status |
|------|--------|
| `CycleTwoChordGraph.tseitinAxioms` | Crossing → `CrossingEndpoints.tseitinAxioms`; noncrossing → chord1/chord2 encoder |
| `defaultOddMarking` / `oddChargeFromMarking` | φ-dependent charge; default = charge 1 on `p0` |
| `tseitinFromMarking` / `tseitinAxiomsFromMarking` | Noncrossing branch uses φ; crossing branch fixed |
| `tseitinAxiomsFromMarking_eq_default` | Default φ recovers legacy `tseitinAxioms` (nested/disjoint) |
| `c5OfoldGraph_tseitinFromMarking_default` / `c8NestedGraph_tseitinFromMarking_default` | Smoke backward compat |
| `tseitinFromAxioms` / `TwoChordSmokeTseitinUnification` | Smoke wiring (c5–c10) |
| `TwoChordWidthContext.ofSmokeUnification` | **Main.lean** factory: smoke unification + tw + width → context |

**Remaining:** crossing branch φ-dependent encoder; proved `width_eq` from axioms (not hypothesis).

### Real max degree Δ = 3 (`CycleTwoChords.lean`)

| Item | Status |
|------|--------|
| `realMaxDegreeThree` / `toSimpleGraph_maxDegree_le_three` | Real `SimpleGraph.maxDegree` predicates |
| `maxDegree_eq_three` | Phase 1 proxy (`4 ≤ n`, always true for valid endpoints) |
| `realMaxDegreeThree_of_graph_eq` | Generic transport from smoke graph equality + `native_decide` |
| `c5/c6/c8/c7/c8/c9/c10` smoke | `native_decide` on computable graph abbrevs + graph eq |

**Phase 5 gap (B1):** `DegreeBounds.lean` — generic **`toSimpleGraph_maxDegree_le` ∀ valid g** and **`isNondegenerate → realMaxDegreeThree`** **proved** (via `cycleGraph ⊔ edge ⊔ edge` + `toSimpleGraph_eq_noncrossing` transport); **`crossing_isDelta3Admissible`** corollary proved. Still open: **`realMaxDegreeThree` without nondegenerate** (degenerate nested/disjoint can have maxDegree = 2).

### Main conditional theorem (`CycleTwoChords/MainTheorem.lean`)

| Item | Status |
|------|--------|
| `cycle_two_chords_resolution_width_conditional` | Main bundle: dichotomy ⇒ width 3/4 by geometry |
| `cycle_two_chords_resolution_width_conditional'` | `if`-then-else alias |
| `ChordWidthPhase5Doc` | Phase 5 documentation string |
| `cycle_two_chords_resolution_width` | **Not proved** — unconditional ∀n hook documented in module header |

---

## Phase 4 — proven (conditional + smoke)

### Crossing width = 4 (`Laws/CrossingWidth4.lean`)

| Item | Status |
|------|--------|
| `CrossingLineGraphTw4` | Structure: tw(L(G)) = 4 hypothesis witness |
| `CrossingWidth4Prediction` | Bundles tw=4 + K₄ core + literature char |
| `crossing_width_eq_four` | Conditional: literature + crossing + K₄ + tw=4 ⇒ width = 4 |
| `c5Smoke_lineGraph_tw4` / `c5Ofold_lineGraph_tw4` | Smoke tw=4 witness (transport via graph eq) |
| `c5Ofold_crossing_lineGraph_tw4` | `CrossingLineGraphTw4` instance on c5Ofold |
| `c5Smoke_lineGraph_edgeSet_card` | \|E(G)\| = 7 on c5 smoke (`native_decide`) |

### Noncrossing width = 3 (`Laws/NoncrossingWidth3.lean`)

| Item | Status |
|------|--------|
| `NoncrossingLineGraphTw3` | Structure: tw(L(G)) = 3 hypothesis witness |
| `NoncrossingWidth3Prediction` | Bundles tw=3 + C₄ core + literature char |
| `noncrossing_width_eq_three` / `noncrossing_width_eq_three_when_tw_eq_three` | Conditional: literature + noncrossing + C₄ + tw=3 ⇒ width = 3 |
| `c8Smoke_lineGraph_tw3` / `c8Nested_lineGraph_tw3` | Smoke tw=3 witness (transport via graph eq) |
| `c8Nested_noncrossing_lineGraph_tw3` | `NoncrossingLineGraphTw3` instance on c8Nested |
| `c8Smoke_lineGraph_edgeSet_card` | \|E(G)\| = 10 on c8 smoke (`native_decide`) |

**Gap closed:** Phase 2 `noncrossing_width_eq_three_when_tw_le_two` assumed tw ≤ 2; Python observes tw = 3. Phase 4 adds the tw = 3 path via `noncrossing_width_eq_three_when_tw_eq_three`.

### Treewidth scaffolding update (`Treewidth.lean`)

| Item | Status |
|------|--------|
| `LineGraphTreewidthEliminationWitness` | Structure bundling tw witness + elimination order |
| `edgeSetUnivEliminationOrder` | Helper (noncomputable; `Finset.univ.toList` on `G.edgeSet`) |
| Line-graph elimination smoke (c5/c8) | **Deferred** — `G.edgeSet` noncomputable blocks `native_decide` on elimination lists |

---

## Phase 3 — proven (smoke + instance)

### Degree-2 suppression (`DegreeTwoSuppression.lean`)

| Item | Status |
|------|--------|
| `isBranchVertex`, `branchVertices`, `suppressDegreeTwoPaths` | Definitions |
| `canonicalSuppressedCore`, `CycleTwoChordGraph.suppressedCore` | Definitions + `suppressedCore_branch_eq` |
| `branchVertices_congr`, `branchVertices_eq_of_graph_eq` | Graph-equality transport (DecidableRel subsingleton) |
| `branchSuppressAdjacent_of_graph_eq` | Suppress-adjacency transport along `G = G'` |
| `canonicalSuppressedCore_branch_eq_of_graph_eq` | Branch set transport |
| `SuppressedCore.branchEdgeCount_eq` | Edge count from branch finset |

### Structural core predicates (`TwoChordCore.lean`)

| Predicate / witness | Meaning | Proof |
|---------------------|---------|-------|
| `SuppressedCore.isK4` | 4 branch verts, all 6 suppress-edges, `branchEdgeCount = 6` | Definition |
| `SuppressedCore.isFourCycle` | 4 branch verts, suppress-degree 2, 4 edges | Definition |
| `c5SmokeSuppressedCore_isK4` | Smoke K₄ on `c5SmokeGraph` | `native_decide` |
| `c8SmokeSuppressedCore_isFourCycle` | Smoke C₄ on `c8SmokeGraph` | `native_decide` |
| `c5Ofold_smokeGraph_eq` / `c8Nested_smokeGraph_eq` | Instance graph = smoke abbrev | Adj extensionality + `native_decide` |
| `c5Ofold_core_isK4` | Instance suppressed core is K₄ | Transport from smoke via graph eq |
| `c8Nested_core_isFourCycle` | Instance suppressed core is C₄ | Transport from smoke via graph eq |
| `c5Ofold_crossing_core_k4` | `CrossingCoreIsK4` witness for c5Ofold | Bundles above |
| `c8Nested_noncrossing_core` | `NoncrossingCoreIsFourCycle` witness for c8Nested | Bundles above |

### Treewidth scaffolding (`Treewidth.lean`)

| Item | Status |
|------|--------|
| `EliminationOrder`, `TreewidthEliminationWitness` | Structures |
| `k4EliminationOrder`, `fourCycleEliminationOrder` | Smoke orders on `Fin 4` |
| `k4TreewidthEliminationWitness`, `fourCycleTreewidthEliminationWitness` | Bundled witnesses (nominal tw 3 / 2) |

---

## Proven (conditional, Phase 1–2)

| Theorem | Meaning |
|---------|---------|
| `width_from_treewidth_of_characterization` | If literature holds and Δ=3, tw(L(G))=k ⇒ width = max(3,k) |
| `two_chord_width_from_characterization` | Same for `CycleTwoChordGraph` + odd marking |
| `noncrossing_width_eq_three_when_tw_le_two` | If tw ≤ 2 and noncrossing ⇒ width = 3 (legacy path; superseded for tw=3 by Phase 4) |
| `crossing_width_prediction_value` / `noncrossing_width_prediction_value` | Branch predictions given core witnesses |

---

## Hypothesis / stub (not PNPLab theorems)

| Item | Status |
|------|--------|
| `TseitinWidthTreewidthCharacterization.width_eq` | **Literature hypothesis** — needs paper verification |
| `TreewidthWitness` / `CrossingLineGraphTw4.tw` / `NoncrossingLineGraphTw3.tw` | Prop stub; tw(L(G)) = 3/4 supplied as explicit witnesses (Python-validated) |
| `maxDegree_eq_three` | Phase 1 proxy (`4 ≤ n`); smoke `realMaxDegreeThree = 3` on c5/c6/c8 via `native_decide` |
| `tseitinFromAxioms` / `TwoChordSmokeTseitinUnification` | Smoke-only constant φ wiring; full odd-marking φ Tseitin open |
| Legacy `CrossingLineGraphTw` / `NoncrossingLineGraphTw` in `TwoChordCore.lean` | Phase 3 stubs (k = 2∨3 / k ≤ 2); superseded by Fase 4 Laws modules |

---

## Phase 4–5 gaps / Phase 5 remaining

1. **`cycle_two_chords_resolution_width`** — unconditional ∀n: Width = 3 ↔ noncrossing (Fase 5 exit criterion)  
2. **Prove tw(L(G)) = 4** (crossing) and **= 3** (noncrossing) for all n — not just hypothesis witnesses  
3. **Line-graph elimination orders** on c5/c8 smoke — blocked by noncomputable `G.edgeSet` / `Finset.toList`  
4. **Full graph isomorphism** — no `SimpleGraph.Iso` to K₄ / C₄; structural predicates only  
5. **Universal ∀n core theorems** — smoke/instance witnesses only for `c5Ofold` / `c8Nested`  
6. **Real treewidth** — replace `TreewidthWitness` stub when Mathlib API lands (PR [#38334](https://github.com/leanprover-community/mathlib4/pull/38334))  
7. **Odd marking φ** — noncrossing `tseitinFromMarking` wired; crossing branch still fixed; full `width_eq` from axioms open  
8. **Unified literature char** — `TwoChordWidthContext.ofSmokeUnification` factory; need `∀ valid g` + proved `width_eq`  
9. **Generic Δ bounds** — **`toSimpleGraph_maxDegree_le` ∀ valid g** and **`isNondegenerate → realMaxDegreeThree`** **proved**; **`realMaxDegreeThree` without nondegenerate** still open (degenerate configs)

---

## External validation

| Artifact | Status |
|----------|--------|
| `reports/LITERATURE_TSEITIN_WIDTH.md` | **Complete** (2026-08-02) — width source = Galesi et al. 2020 |
| `reports/chord_treewidth_verification.csv` | **Complete** (2026-08-03 rerun) — n=5..100, 383 Δ=3 witnesses |
| `reports/CHORD_TREewidth_VERIFICATION.md` | **Complete** — 383/383 match (representative n=5..100; rerun 2026-08-03) |
| `reports/CHORDWIDTH_INTEGRATION_SUMMARY.md` | **Complete** — one-page Lean + Python + literature integration |
| `reports/chord_treewidth_exact_n5_n14.csv` | **Complete** (2026-08-03) — **2870/2870** exact, 0 counterexamples |
| `reports/CHORD_TREewidth_EXACT_N5_N14.md` | **Complete** — gap-pattern sweep n=5..14 |
| `reports/COMMUNITY_QUESTION_DRAFT.md` | **Complete** — Zulip + MathOverflow drafts |
| `reports/ZULIP_MESSAGE_READY.txt` | **Complete** — copy-paste #mathlib4 ([Zulip + Mathlib](e4bc602c-a14c-4005-9458-ed4f96111e68)) |
| `reports/MATHOVERFLOW_MESSAGE_READY.txt` | **Complete** — ready MO post |
| `reports/MATHLIB_TW_STATUS.md` | **Complete** — PR #38334 still open (Aug 2026) |
| `reports/ZULIP_POSTING_GUIDE.md` | **Complete** — pasos EN/ES |
| `reports/FASE5_ROADMAP.md` | **Complete** — teorema ∀n, timeline |

### Python treewidth — representative n=15..16 (2026-08-03)

`scripts/verify_chord_treewidth.py --n-lo 15 --n-hi 16 --representative`: **8/8** match, 0 mismatches, ~0.01s. No MemoryError.

### Python treewidth — representative (2026-08-03 rerun)

`scripts/verify_chord_treewidth.py`, n=5..100: **383/383** match in **14.1s** (heuristic tw for n≥9; 17 exact for n≤8). See [CHORDWIDTH_INTEGRATION_SUMMARY.md](CHORDWIDTH_INTEGRATION_SUMMARY.md).

**Memory guard (2026-08-03):** `--memory-safe` (default on) skips `exact_width_search` when |V(L(G))| > 14; n=15..20 trial hit `MemoryError`. Exact boundary remains n≤14 (2870 configs).

| Geometry | tw(L(G)) | configs |
|----------|----------|--------:|
| noncrossing | **3** | 191 |
| crossing | **4** | 192 |

### Python treewidth — exact sweep n=5..14 (2026-08-03)

| Geometry | tw(L(G)) | configs |
|----------|----------|--------:|
| noncrossing | **3** | 1870 |
| crossing | **4** | 1000 |

**2870/2870 exact matches, 0 counterexamples, ~17 min.**

**Phase 4 gate:** tw(L(G))=3/4 **exact-validated** on all Δ=3 gap configs for n≤14; Lean Phase 4 records hypothesis witnesses + conditional width theorems on smoke instances.

---

## Build commands

```powershell
cd lean
$env:LEAN_NUM_THREADS = "2"
lake build PNPLab.ChordWidth.Main
```

**Do not** run parallel `lake build PNPLab` (OOM risk on full tree).
