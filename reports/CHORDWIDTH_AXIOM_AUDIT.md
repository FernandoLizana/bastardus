# ChordWidth Axiom Audit

**Scope:** new/changed theorems this session + representative existing theorems

---

## Method

Lean command (manual): `#print axioms <theorem>`

ChordWidth files: **no local `axiom` declarations** (grep verified).

---

## Expected axioms (Mathlib standard)

| Axiom | Expected |
|-------|----------|
| `propext` | yes |
| `Classical.choice` | yes |
| `Quot.sound` | yes |

Certificate proofs using `native_decide` compile to kernel-checked computation — no new axioms.

---

## Project assumptions (not Lean axioms)

| Assumption | Location | Type |
|------------|----------|------|
| Galesi width formula | `TseitinWidthTreewidthCharacterization` | **Structure field** (hypothesis) |
| tw(L(G)) value | `LineGraphTwBound.certified` | **Proof** (finite) or **experimental** |
| Literature char | `TwoChordWidthContext.char` | **Hypothesis** |

These are **logical assumptions**, correctly labeled CONDITIONAL in theorems.

---

## Theorems to audit when G1 closes

- `lineGraph_hasTreeDecomp_three_of_noncrossing` (future)
- `#print axioms` on any universal tw equality theorem

---

## Session additions

| Theorem | sorry | Local axioms |
|---------|-------|--------------|
| `cyclicGaps_sum` | 0 | 0 |
| `cyclicGap_pos` | 0 | 0 |

---

## Suspicious patterns (none found)

- No `sorry`/`admit` in ChordWidth lean tree
- No custom axioms smuggling tw values
