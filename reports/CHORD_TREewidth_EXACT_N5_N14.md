# Chord line-graph treewidth verification

**Generated:** 2026-08-03 16:35:25 UTC
**Range:** n = 5..14
**Runtime:** 1012.81s
**Valid Δ=3 configurations checked:** 2870
**Skipped (Δ≠3 or degenerate chords):** 130

## Conjecture

For G = C_n + two chords (four distinct endpoints, Δ = 3):

| Geometry | Expected tw(L(G)) |
|----------|-------------------|
| non-crossing | 3 |
| crossing | 4 |

## Summary

- **Matches:** 2870 / 2870
- **Mismatches (counterexamples):** 0
- **Timed out:** 0

### Observed tw(L(G)) by crossing flag

| crosses | tw | count |
|---------|----|-------|
| False | 3 | 1870 |
| True | 4 | 1000 |

### Treewidth methods used

| method | count |
|--------|-------|
| exact_bruteforce | 56 |
| exact_width_search | 2814 |

## Sample results (first 12 rows)

| n | pairing | crosses | tw | expected | match | method | chord_spec |
|---|---------|---------|----|-----------|-------|--------|------------|
| 5 | crossing | True | 4 | 4 | True | exact_bruteforce | (0,2)+(1,3) |
| 5 | nested | False | 3 | 3 | True | exact_bruteforce | (0,3)+(1,2) |
| 5 | crossing | True | 4 | 4 | True | exact_bruteforce | (0,2)+(1,4) |
| 5 | disjoint | False | 3 | 3 | True | exact_bruteforce | (0,1)+(2,4) |
| 5 | crossing | True | 4 | 4 | True | exact_bruteforce | (0,3)+(1,4) |
| 5 | nested | False | 3 | 3 | True | exact_bruteforce | (0,4)+(1,3) |
| 5 | crossing | True | 4 | 4 | True | exact_bruteforce | (0,3)+(2,4) |
| 5 | disjoint | False | 3 | 3 | True | exact_bruteforce | (0,2)+(3,4) |
| 6 | crossing | True | 4 | 4 | True | exact_bruteforce | (0,2)+(1,3) |
| 6 | nested | False | 3 | 3 | True | exact_bruteforce | (0,3)+(1,2) |
| 6 | crossing | True | 4 | 4 | True | exact_bruteforce | (0,2)+(1,4) |
| 6 | nested | False | 3 | 3 | True | exact_bruteforce | (0,4)+(1,2) |

## Counterexamples

None found in this run.

## Method notes

- Graph builder: `networkx.cycle_graph(n)` + two chord edges.
- Crossing test: `backend.proof_complexity.chord_crossing_law.chords_cross_on_cycle`.
- Line graph: `networkx.line_graph`.
- Exact treewidth (bruteforce elimination) when |V(L(G))| ≤ 32; otherwise NetworkX min-degree / min-fill-in **upper bound** (not exact).
- PyPI package `treewidth` is unavailable; local module `scripts/treewidth` is used.
- Default: `--representative` (fast C5/C6 witnesses; gap fallback for n≤16 only).
- Gap-pattern sweep (`--no-representative`): rotation-normalized, O(n³) per n.
- Full C(n,4) (`--full-endpoints`): capped at n≤16 even with explicit flag.
- Representative mode never uses C(n,4) unless `--full-endpoints`; n>16 uses witnesses only.

CSV: `reports/chord_treewidth_exact_n5_n14.csv`
