# ChordWidth AI Final Report

**Date:** 2026-08-04  
**Branch:** `research/chordwidth-universal-ai`  
**Honesty classification:** **PARTIAL FORMAL PROGRESS**

---

## A. Executive summary

Audited the full ChordWidth pipeline, formalized the problem statement, ran adversarial counterexample search (0 found in n=5..14 among 2870 valid configs), selected **path decomposition on cyclic arcs** as primary proof route, and added a **universal Lean lemma** (`cyclicGaps_sum`) toward noncrossing tw(L(G)) ≤ 3.

**G1, G2, G5 remain OPEN.** No universal tw dichotomy proved. Build stays green (1271 jobs).

---

## B. Gap status

| Gap | Initial | Final | Evidence | Main file |
|-----|---------|-------|----------|-----------|
| G1 tw dichotomy ∀n | OPEN | **OPEN** | 2870/2870 Python; 10 smokes + certs finite | `TreeDecomp/Certificates*.lean` |
| G2 core K4/C4 ∀n | OPEN | **OPEN** | Structural isK4 smoke only | `TwoChordCore.lean` |
| G5 Tseitin crossing | OPEN | **OPEN** | CrossingEndpoints bridge partial | `TseitinEncoding.lean` |

---

## C. Theorem status

| Theorem | Status | Compiles | sorry-free | Universal |
|---------|--------|:--------:|:----------:|:---------:|
| `cycle_two_chords_resolution_width_conditional` | CONDITIONAL | ✅ | ✅ | ❌ |
| Smoke `HasTreeDecomp` (10) | PROVED finite | ✅ | ✅ | ❌ |
| `cyclicGaps_sum` | **PROVED** | ✅ | ✅ | **✅** |
| `cyclicGap_pos` | **PROVED** | ✅ | ✅ | **✅** |
| tw(L(G))=3/4 ∀n | OPEN | — | — | — |

---

## D. Computational results

| Sweep | Range | Valid | Counterexamples | Exact tw |
|-------|-------|------:|----------------:|----------|
| New adversarial script | n=5..14 | 2870 | 0 | partial (1296 heuristic in fast run) |
| Prior verify_chord_treewidth | n=5..14 | 2870 | 0 | exact (documented) |

---

## E. Best mathematical route

**Route F+A:** Path/tree decomposition sliding bags along four cyclic arcs (gaps sum to n). Sketch: `notes/proofs/noncrossing_path_decomp_sketch.md`.

Lower bounds (Route C) still required for equality.

---

## F. Lean deliverables

**Added:**
- `lean/PNPLab/ChordWidth/BaseCaseTwoChords/ArcLengths.lean`
- `scripts/chordwidth/search_two_chord_counterexamples.py`
- `notes/proofs/noncrossing_path_decomp_sketch.md`
- `reports/CHORDWIDTH_AI_*.md` (9 files)
- `experiments/chordwidth_ai/*.json`
- `experiments/chordwidth_counterexamples/*.json`

**Modified:**
- `lean/PNPLab/ChordWidth/BaseCaseTwoChords/Main.lean` (import ArcLengths)

**Build:** 1271/1271 jobs SUCCESS

---

## G. Tseitin crossing

Encoder crossing remains **partial** via `CrossingEndpoints`; not symmetric with noncrossing pipeline. G5 **not closed**.

---

## H. Closure honesty

**PARTIAL FORMAL PROGRESS**

Not: THEOREM UNIVERSALLY PROVED, not COMPUTATIONAL EVIDENCE ONLY (there is new universal Lean lemma).

---

## I. Next exact action

**Formalize edge-count per cyclic arc** as a function of `cyclicGap 0..3` and pairing, in Lean — prerequisite for parametric `noncrossingLineGraphDecomp`.

---

## Reproduce

```powershell
git checkout research/chordwidth-universal-ai
cd lean
$env:LEAN_NUM_THREADS="2"
lake build PNPLab.ChordWidth.Main

cd ..
$env:PYTHONPATH="scripts"
python scripts/chordwidth/search_two_chord_counterexamples.py --n-lo 5 --n-hi 14 --memory-safe
```
