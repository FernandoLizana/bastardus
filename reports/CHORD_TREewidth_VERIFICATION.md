# Chord line-graph treewidth verification

**Generated:** 2026-08-03 22:14:42 UTC
**Range:** n = 15..16
**Runtime:** 0.01s
**Valid Δ=3 configurations checked:** 8
**Skipped (Δ≠3 or degenerate chords):** 0

## Conjecture

For G = C_n + two chords (four distinct endpoints, Δ = 3):

| Geometry | Expected tw(L(G)) |
|----------|-------------------|
| non-crossing | 3 |
| crossing | 4 |

## Summary

- **Matches:** 8 / 8
- **Mismatches (counterexamples):** 0
- **Timed out:** 0

### Observed tw(L(G)) by crossing flag

| crosses | tw | count |
|---------|----|-------|
| False | 3 | 4 |
| True | 4 | 4 |

### Treewidth methods used

| method | count |
|--------|-------|
| networkx_upper_bound | 8 |

## Sample results (first 12 rows)

| n | pairing | crosses | tw | expected | match | method | chord_spec |
|---|---------|---------|----|-----------|-------|--------|------------|
| 15 | crossing | True | 4 | 4 | True | networkx_upper_bound | (0,2)+(1,3) |
| 15 | nested | False | 3 | 3 | True | networkx_upper_bound | (0,3)+(1,2) |
| 15 | crossing | True | 4 | 4 | True | networkx_upper_bound | (0,4)+(2,5) |
| 15 | nested | False | 3 | 3 | True | networkx_upper_bound | (0,5)+(2,3) |
| 16 | crossing | True | 4 | 4 | True | networkx_upper_bound | (0,2)+(1,3) |
| 16 | nested | False | 3 | 3 | True | networkx_upper_bound | (0,3)+(1,2) |
| 16 | crossing | True | 4 | 4 | True | networkx_upper_bound | (0,4)+(2,5) |
| 16 | nested | False | 3 | 3 | True | networkx_upper_bound | (0,5)+(2,3) |

## Counterexamples

None found in this run.

## Method notes

- Graph builder: `networkx.cycle_graph(n)` + two chord edges.
- Crossing test: `backend.proof_complexity.chord_crossing_law.chords_cross_on_cycle`.
- Line graph: `networkx.line_graph`.
- Exact treewidth (bruteforce elimination) when |V(L(G))| ≤ 10; otherwise NetworkX min-degree / min-fill-in **upper bound** (not exact).
- ``exact_width_search`` (|V| > 8) skipped when |V| > 14 and ``--memory-safe`` is on (default): n=15..20 trial hit MemoryError.
- PyPI package `treewidth` is unavailable; local module `scripts/treewidth` is used.
- Default: `--representative` (fast C5/C6 witnesses; gap fallback for n≤16 only).
- Gap-pattern sweep (`--no-representative`): rotation-normalized, O(n³) per n.
- Full C(n,4) (`--full-endpoints`): capped at n≤16 even with explicit flag.
- Representative mode never uses C(n,4) unless `--full-endpoints`; n>16 uses witnesses only.

CSV: `reports/CHORD_TREewidth_VERIFICATION.md`
