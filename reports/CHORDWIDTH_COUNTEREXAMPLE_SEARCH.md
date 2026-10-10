# ChordWidth Counterexample Search

**Script:** `scripts/chordwidth/search_two_chord_counterexamples.py`  
**Run:** 2026-08-04, branch `research/chordwidth-universal-ai`

---

## Conjecture tested

For **valid** configs (max degree 3 on `G`):

| Branch | Expected tw(L(G)) |
|--------|-------------------|
| crossing | 4 |
| nested/disjoint | 3 |

---

## Results (this run)

| Metric | Value |
|--------|-------|
| n range | 5 .. 14 |
| Total gap-pattern configs | 3000 |
| Valid (Δ=3) | **2870** |
| Degenerate skipped | 130 |
| Crossing valid | 1000 |
| Noncrossing valid | 1870 |
| **Counterexamples** | **0** |
| Wall time | ~100 s |
| Status | `NO_COUNTEREXAMPLE_IN_RANGE` |

Artifacts:

- `experiments/chordwidth_counterexamples/results.json`
- `experiments/chordwidth_counterexamples/reproducibility.json`

---

## Method caveats (honest)

1. **1296/2870** valid instances used **non-exact** tw methods in this run (`memory_safe` + |V(L)|>14 guard inside n≤14 sweep for larger line graphs).
2. Prior repo evidence: `scripts/verify_chord_treewidth.py --no-representative --n-lo 5 --n-hi 14` claims **2870/2870 exact** — prefer that for exact claims.
3. This script does **not** prove ∀n.
4. **disjoint** pairing included in noncrossing bucket (matches Python convention).

---

## Degenerate cases observed

130 configs with max degree ≠ 3 (typically chords coinciding with cycle edges). These are **excluded** from conjecture test — aligns with `isNondegenerate` / Python filter.

---

## Conclusion

**No counterexample found** in gap-pattern enumeration n=5..14 among Δ=3 configs.

**Classification:** SUPPORTED BY EXPERIMENTS — **not** PROVED.

If a counterexample is found in future runs, minimal config will be printed and stored in `results.json` → status `REFUTED`.

---

## Reproduce

```powershell
$env:PYTHONPATH="scripts"
python scripts/chordwidth/search_two_chord_counterexamples.py --n-lo 5 --n-hi 14 --memory-safe

# Exact tw (slower, authoritative for n≤14):
python scripts/verify_chord_treewidth.py --n-lo 5 --n-hi 14 --no-representative --memory-safe
```
