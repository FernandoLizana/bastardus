# ChordWidth integration summary

**Updated:** 2026-08-03 (Tseitin φ extension + 1077-job build)  
**Scope:** Lean Phase 3/4 status, Python validation (2870 + 383), literature, community outreach, recommended next steps.

---

## At a glance

| Track | Status | Artifact |
|-------|--------|----------|
| **Lean Phase 3** | Green — structural K₄/C₄ smoke, degree-2 suppression | [CHORD_WIDTH_LEAN_STATUS.md](CHORD_WIDTH_LEAN_STATUS.md) |
| **Lean Phase 5 scaffold** | Green — certs 10/10, ArcLengths, EdgeIndexing, NoncrossingPathDecomp; **1273 jobs** | [CHORDWIDTH_AI_FINAL_REPORT.md](CHORDWIDTH_AI_FINAL_REPORT.md) |
| **Lean Phase 4** | Conditional width laws + smoke tw witnesses (hypothesis stubs); real ∀n tw bounds open | [CHORD_WIDTH_LEAN_STATUS.md](CHORD_WIDTH_LEAN_STATUS.md) §Phase 4 |
| **Python exact** | **2870/2870** (n=5..14, gap sweep, 0 counterexamples) | [CHORD_TREewidth_EXACT_N5_N14.md](CHORD_TREewidth_EXACT_N5_N14.md) |
| **Python representative n=15..16** | **8/8** (selective, 0.01s, no MemoryError) | this session |
| **Python representative** | **383/383** (n=5..100, rerun 2026-08-03, 14.1s) | [CHORD_TREewidth_VERIFICATION.md](CHORD_TREewidth_VERIFICATION.md) |
| **Literature** | Width identity = Galesi–Talebanfard–Torán (TOCT 2020) | [LITERATURE_TSEITIN_WIDTH.md](LITERATURE_TSEITIN_WIDTH.md) |
| **Community** | Zulip + MathOverflow drafts ready | [COMMUNITY_QUESTION_DRAFT.md](COMMUNITY_QUESTION_DRAFT.md) |

---

## Lean: Phase 3–5 scaffold, unconditional ∀n open

**Phase 3 (proved):** Degree-2 suppression, structural K₄/C₄ smoke witnesses. Build green, no `sorry`.

**Phase 4 (conditional + smoke):** Width = 4/3 given literature + tw witnesses + cores (`Laws/CrossingWidth4`, `Laws/NoncrossingWidth3`).

**Phase 5 (conditional per-instance):** `cycle_two_chords_resolution_width_conditional` — crossing ⇒ width 4, noncrossing ⇒ width 3 for fixed graph + φ. `TseitinEncoding.lean`: `oddChargeFromMarking`, `tseitinFromMarking` (noncrossing φ); `TwoChordWidthContext.ofSmokeUnification` in Main.

**Still open (B1–B4):** Unconditional `cycle_two_chords_resolution_width` ∀n; real tw(L(G)) proofs; core iso; Mathlib PR [#38334](https://github.com/leanprover-community/mathlib4/pull/38334). **B1 (Δ=3) closed** for nondegenerate configs: `isNondegenerate → isDelta3Admissible` proved; degenerate nested/disjoint (maxDegree = 2) excluded by Python filter.

**Build:** `lake build PNPLab.ChordWidth.Main` — **1077/1077 green** (2026-08-03). Do not parallel-build full PNPLab tree — OOM risk.

**Smoke Δ=3:** c5–c10 crossing + noncrossing representatives; Python n=7..10 representative **16/16** match (2026-08-03).

---

## Python validation

### Exact sweep — n = 5..14 (2870 configs)

Gap-pattern rotation-normalized enumeration; `--exact-max-nodes 32`. All Δ=3 configs checked:

| Geometry | tw(L(G)) | count |
|----------|----------|------:|
| noncrossing | 3 | 1870 |
| crossing | 4 | 1000 |

**2870/2870 exact matches, 0 counterexamples** (~17 min). Script hardened: treewidth bitset degree bug fixed; no C(n,4) without `--full-endpoints`.

### Representative sweep — n = 5..100 (383 configs)

One crossing + one non-crossing witness per n (fast C5/C6 shapes; gap fallback for n≤16 only). **Rerun 2026-08-03:** **383/383 matches in 14.1s** — counts unchanged from prior run.

| Method | count |
|--------|------:|
| exact_bruteforce | 9 |
| exact_width_search | 8 |
| networkx_upper_bound | 366 |

For n≥9 most checks use NetworkX min-degree / min-fill-in **upper bounds** (not exact). No counterexamples observed; heuristic upper bounds agree with conjecture tw ∈ {3, 4}.

### Optional n = 15..16 selective — completed

Representative `--n-lo 15 --n-hi 16`: **8/8** match in 0.01s; no MemoryError. Full exact sweep n=15+ still blocked by memory on `exact_width_search`.

**Conjecture (Phase 3/4 gate):** For G = C_n + two chords (four distinct endpoints, Δ = 3): noncrossing ⇒ tw(L(G)) = 3; crossing ⇒ tw(L(G)) = 4.

**Reproduce:**

```powershell
# Representative n=5..100 (~15s)
python scripts/verify_chord_treewidth.py --n-lo 5 --n-hi 100 --representative

# Exact gap sweep n=5..14 (~17 min)
python scripts/verify_chord_treewidth.py --n-lo 5 --n-hi 14 --no-representative --exact-max-nodes 32 `
  --csv reports/chord_treewidth_exact_n5_n14.csv --md reports/CHORD_TREewidth_EXACT_N5_N14.md
```

---

## Literature (Galesi et al.)

PNPLab's width hypothesis is **not** original: the exact Tseitin resolution width formula

\[
w(T(G,\varphi)) = \max\{\Delta(G),\, \mathrm{tw}(L(G))\}
\]

is **Galesi–Talebanfard–Torán, TOCT 2020**. Ben-Sasson–Wigderson, de Colnet–Mengel, and Itsykson et al. support size/automatizability bounds but do not state this width identity. No cited paper covers C_n + two chords explicitly; our case is covered indirectly via Δ = 3 and tw(L(G)) bounds.

Full audit: [LITERATURE_TSEITIN_WIDTH.md](LITERATURE_TSEITIN_WIDTH.md). Paper draft: [CHORD_DIAGRAM_TSEITIN_WIDTH.md](../papers/CHORD_DIAGRAM_TSEITIN_WIDTH.md).

---

## Community draft

Ready-to-paste posts:

- **Zulip (#mathlib4):** [ZULIP_MESSAGE_READY.txt](ZULIP_MESSAGE_READY.txt) — context + Questions A & B.
- **MathOverflow:** [MATHOVERFLOW_MESSAGE_READY.txt](MATHOVERFLOW_MESSAGE_READY.txt).
- **Mathlib treewidth status:** [MATHLIB_TW_STATUS.md](MATHLIB_TW_STATUS.md) (PR #38334, Aug 2026).
- **Full drafts / Question C:** [COMMUNITY_QUESTION_DRAFT.md](COMMUNITY_QUESTION_DRAFT.md). Posting guide: [ZULIP_POSTING_GUIDE.md](ZULIP_POSTING_GUIDE.md).

---

## Next steps for user

1. **Post Zulip (#mathlib4)** — copy-paste [ZULIP_MESSAGE_READY.txt](ZULIP_MESSAGE_READY.txt) (context + Questions A & B). Walkthrough: [ZULIP_POSTING_GUIDE.md](ZULIP_POSTING_GUIDE.md). Do **not** claim 2870/2870 or 383/383 as proofs — label as computational evidence.
2. **(Optional) Post MathOverflow** — copy-paste [MATHOVERFLOW_MESSAGE_READY.txt](MATHOVERFLOW_MESSAGE_READY.txt); add tags and references as listed.
3. **Read Phase 4–5 roadmap** — [FASE5_ROADMAP.md](FASE5_ROADMAP.md) for exit criteria, pathwidth vs treeWidth trade-offs, and Lean Phase 4a–d ordering.
4. **Track Mathlib treewidth PR** — monitor [#38334](https://github.com/leanprover-community/mathlib4/pull/38334) status in [MATHLIB_TW_STATUS.md](MATHLIB_TW_STATUS.md); do not upgrade pin until merge unless explicitly tracking the PR branch.
5. **Keep Python as regression gate** — rerun representative sweep after script changes; exact n=5..14 before major refactors (`scripts/verify_chord_treewidth.py`).
6. **Lean Phase 4a (after #38334)** — replace `TreewidthWitness` stubs with Mathlib `SimpleGraph.treeWidth`; build with `lake build PNPLab.ChordWidth.Main` only (avoid full PNPLab tree — OOM risk).
7. **Lean Phase 4b–d** — pursue ∀n core classification and tw(L(G)) bounds (elimination orders on L(G) or outerplanar arguments); see [CHORD_WIDTH_LEAN_STATUS.md](CHORD_WIDTH_LEAN_STATUS.md).
8. **Do not expand Lean tree imports** — ChordWidth stays isolated from 461-case PNPLab catalog until Fase 5 universal theorem is ready.

Soundness audit: [CROSSING_LAW_SOUNDNESS_AUDIT.md](CROSSING_LAW_SOUNDNESS_AUDIT.md). Full outreach drafts: [COMMUNITY_QUESTION_DRAFT.md](COMMUNITY_QUESTION_DRAFT.md).

---

## Related documents

| Document | Role |
|----------|------|
| [CHORD_WIDTH_LEAN_STATUS.md](CHORD_WIDTH_LEAN_STATUS.md) | Lean module layout, Phase 3 checklist, build commands |
| [CHORD_TREewidth_VERIFICATION.md](CHORD_TREewidth_VERIFICATION.md) | 383/383 representative report |
| [CHORD_TREewidth_EXACT_N5_N14.md](CHORD_TREewidth_EXACT_N5_N14.md) | 2870/2870 exact report |
| [LITERATURE_TSEITIN_WIDTH.md](LITERATURE_TSEITIN_WIDTH.md) | Galesi width theorem + paper map |
| [COMMUNITY_QUESTION_DRAFT.md](COMMUNITY_QUESTION_DRAFT.md) | Zulip / MO outreach |
| [FASE5_ROADMAP.md](FASE5_ROADMAP.md) | Phase 4–5 timeline and exit criteria |
