# Sketch: parametric path decomposition for noncrossing tw(L(G)) ≤ 3

**Status:** PARTIAL — fixed 7-node templates infeasible; **generic redesign** in `reports/CHORDWIDTH_GENERIC_DECOMP_DESIGN.md`

## Lean progress (2026-08-05)

- ✅ `EdgeIndexing.lean`, blocks 1–5, conditional assembly scaffold
- ✅ **Generic edge mem:** `cyclicEdgeInGraph_of`, `graphEdgeSym2_mem`, `arcConsecutive_lineGraphAdj`
- ⚠️ c8 Route F+A discharge **parked** (use `CertificatesLine` for c8 tw=3)
- ⬜ Parametric tree `GenericDecompNode g` + open-goals discharge
- ⬜ Lower bound tw(L(G)) ≥ 3

## Decision (2026-08-05)

**Selected path (c):** defer c8 Fin-table discharge; redesign Route F+A with pairing/gap-parametric tree topology (not 6/7-node fixed templates). See design doc.

## Blockers (updated)

1. ~~Edge indexing / cycle mem~~ → **done** (`graphEdgeSym2_mem`)
2. **Tree topology:** derive hub nodes from (pairing, cyclicGap); c8 needs ≥6 edges at one hub under fork
3. Lower bound tw(L(G)) ≥ 3 — **not started**

## Inputs

- Valid `CycleTwoChordGraph` with `isDelta3Admissible` and `¬ chordsCross` (nested or disjoint).
- Four cyclic gaps `g0,g1,g2,g3 > 0`, `g0+g1+g2+g3 = n` (Lean: `ArcLengths.lean`).

## Line graph vertices

Vertices of `L(G)` are edges of `G`: cycle edges on each arc plus the two chord edges.

## Proposed path index

Order bags along a path whose nodes correspond to:
1. sliding windows on each cyclic arc (one bag per cycle edge on long arcs);
2. chord-local bags covering intersections of chord edges with adjacent cycle edges.

Target: bag size ≤ 4 ⇒ width ≤ 3.

## Blockers before Lean

1. Explicit bijection between `Fin (|E(G)|)` and edge labels (stable edge order).
2. Lemma: subdividing a degree-2 path on the primal side → controlled patch on `L(G)`.
3. Lower bound `tw(L(G)) ≥ 3` (minor/bundle witness) for equality.

## Next Lean lemma

Extend `ArcLengths.lean` with edge-count on each arc as function of gaps + pairing.
