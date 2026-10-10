# ChordWidth Adversarial Proof Audit

**Date:** 2026-08-04

---

## Questions applied to current "proved" claims

| Question | Finding |
|----------|---------|
| Proved for all n? | **No** for tw dichotomy — only finite certs + Python |
| Vacuous hypotheses? | `maxDegree_eq_three` only needs n≥4 — weak vs Δ=3 |
| Valid ⊂ conclusion? | `TwoChordWidthContext.char` assumes width identity |
| Crossing definition changed? | No — still `pairing = crossing` |
| Bound on G vs L(G)? | Certificates correctly on line graph |
| Width = \|bag\|-1? | Yes, consistent in `TreeDecomp.width` |
| Got ≤ instead of =? | `HasTreeDecomp k` is upper bound; equality needs lower bound |
| Finite cert smuggled as universal? | **Risk mitigated** — docs label FINITE; mission adds explicit OPEN |
| Unauthorized axioms? | None local; Galesi is explicit structure |

---

## Smoke certificate audit

- 10/10 smokes: `HasTreeDecomp` via iso transport — **valid for those graphs only**.
- `native_decide` used only for bag coverage on Fin types — acceptable for **instance** proofs.

---

## New lemma audit (`ArcLengths.lean`)

| Theorem | Universal? | Sound? |
|---------|------------|--------|
| `cyclicGap_pos` | ✅ ∀ g | ✅ from ordered |
| `cyclicGaps_sum` | ✅ ∀ g | ✅ omega |

No smuggled conclusions.

---

## Verdict on closing G1/G2/G5

| Gap | Can mark closed? |
|-----|------------------|
| G1 | **NO** |
| G2 | **NO** |
| G5 | **NO** |

---

## Attack vectors if claiming false closure

1. Produce n=15 counterexample (exact tw) — search ongoing.
2. Show disjoint degenerate satisfies `TwoChordWidthContext` with wrong width — filter audit needed.
3. Prove `isK4` does not imply tw(L(G))≥4 — would break route D.

None succeeded in this session.
