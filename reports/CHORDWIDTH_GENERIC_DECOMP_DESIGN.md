# ChordWidth G1 — Generic Route F+A Decomposition Design

**Date:** 2026-08-05 | **Route:** F+A parametric redesign (path **c**)  
**Status:** Design + Lean scaffolding; c8 discharge **deferred** (CertificatesLine keeps tw=3)

---

## Problem statement

Prove `HasTreeDecomp (lineGraph G) 3` for every valid noncrossing `CycleTwoChordGraph` G.

The fixed-template pilot (`globalDecompNodeCount = longArcLen + 5`, `certPathGraph` path/fork) is **exhausted** for c8:

| Template | Blocker |
|----------|---------|
| 6-node path | k=5,6 non-interval node sets |
| 7-node path | 0 interval solutions (search 7–10) |
| 7-node fork (junc₁ hub) | Running intersection needs 6 edges at hub → width 5 |

**Conclusion:** Tree topology must be **parametric**, not a fixed node count.

---

## Inputs (combinatorial parameterization)

From `CycleTwoChordGraph`:

| Parameter | Source | Role |
|-----------|--------|------|
| `n, p0..p3` | structure | Four ordered endpoints |
| `pairing` | crossing / nested / disjoint | Chord endpoints + `endpointArcIdx` |
| `cyclicGap 0..3` | `ArcLengths.lean` | Arc lengths; sum = n |
| `longArcIdx` | max gap tie-break | Which arc gets sliding-window segment bags |
| `nonLongArcIdx longArcIdx` | 3 short arcs | Short-arc bag families |

Noncrossing assumptions: `¬ chordsCross`, `isDelta3Admissible`, `isNondegenerate`.

Line-graph vertices: `Fin (n+2)` edge indices (`graphEdgeSym2`), mapped via `GraphEdgeBijection` when inj/surj available.

---

## Bag families (already PROVED in Lean)

These are **pairing-aware** and **width-independent of n** (card ≤ 4 ⇒ width ≤ 3):

1. **Long-arc sliding bags** — `longArcSlidingBag a j` along arc `a` (prev/current/next cycle edge + optional chord at endpoints).
2. **Short-arc sliding bags** — same template on the three non-long arcs.
3. **Chord junction bags** — `{cycle edge at endpoint, chord edge}` (card 2).
4. **Enriched junction bags** — junction ∪ incoming cycle edge ∪ short-arc tail OR long-arc tail (card ≤ 4, proved).

Width lemmas: `longArcBag_width_le_three`, `shortArcBag_width_le_three`, `junctionEnrichedCardLeFour`.

---

## Generic tree topology T (design)

Replace `certPathGraph (longArcLen + 5)` with a **typed decomposition tree** whose node set is a **disjoint union of segments**, not a single Fin (L+5).

### Node kinds

```
T = LongSeg(longArcIdx, j)     for j : Fin (cyclicGap longArcIdx)
  | ShortSeg(a, j)             for a ∈ nonLongArcIdx, j : Fin (cyclicGap a)
  | Junction(e)                for e : Fin 4  (four chord endpoints)
  | Hub(kind)                  optional relay/split nodes (count depends on pairing)
```

### Intended tree shape (pairing-dependent)

**Nested / disjoint (noncrossing):** long arc is a path of `LongSeg` nodes. Each short arc contributes either:
- zero dedicated nodes (length-1 arc covered by enriched junction only), or
- a chain of `ShortSeg` nodes glued to the endpoint junction that owns that arc.

**Crossing (future):** expect extra hub nodes near the K₄-type core; width budget rises to 4.

### Adjacency rules (combinatorial, not fixed Fin length)

| Edge in T | When |
|-----------|------|
| `LongSeg j — LongSeg (j+1)` | consecutive on long arc |
| `LongSeg 0 — Junction(e₀)` | long arc start meets endpoint e₀ |
| `LongSeg (L-1) — Junction(e₁)` | long arc end meets endpoint e₁ |
| `ShortSeg 0 — Junction(e)` | short arc owned by endpoint e (`junctionShortArcAt`) |
| `Junction(e) — Hub(...)` | only when enriched bag alone cannot satisfy running intersection for cross-junction L(G) edges |

**Key design constraint:** Running intersection on tree decompositions requires `{w | v ∈ bag(w)}` **connected in T** for every L(G) vertex v. The c8 fork failure shows that **bare membership** (without connected supersets) fails; hubs must be introduced **only where combinatorics forces them**, not at a fixed index.

### Bag assignment rule

| Node | Bag on L(G) |
|------|-------------|
| `LongSeg j` | `longArcLineGraphBag j` (image of `longArcSlidingBag`) |
| `ShortSeg a j` | `shortArcLineGraphBag a j` |
| `Junction e` | `enrichedJunctionBag e` (± bridge/trim when hub topology fixed) |
| `Hub h` | **Relay bag**: edges that must appear together for RI but span multiple junctions |

Bridge/trim (`globalJunctionPathBridgeBag`, `globalJunctionPathTrimBag`) remain **stubs** until hub placement is derived from pairing + gap vector.

---

## Running intersection strategy

1. **Path segments:** For each arc chain, use interval property on a path subgraph (existing `certPathGraph_induce_interval_preconnected`).
2. **Junction-local edges:** Covered by enriched junction bag (proved card bound).
3. **Cross-junction edges** (e.g. c8 edges 1–3, 5–9 through multiple endpoints): require either:
   - (a) **Hub node** whose bag is the connected superset of involved junction bags, with width ≤ 4, or
   - (b) **Tree split** placing a dedicated relay between junction subtrees (8+ nodes), or
   - (c) **Redistribute** edges into long/short segment bags so each L(G) edge’s node set is an interval on T.

**c8 witness:** fork hub junc₁ needs `{1,3,5,6,8,9}` (card 6) for connected supersets → width 5. Any generic design must **predict** hub cardinality from pairing + gaps before Lean discharge.

---

## Open goals bundle (unchanged semantics)

`NoncrossingPathDecompOpenGoals` fields remain the contract:

- `junction_edgeCover`, `shortArc_edgeCover`, `global_edgeCover`, `global_vertexCover`
- `global_preconnected`, `global_tree`

**Change:** `globalDecompGraph` / `globalBagFamily` should be replaced by **parametric** `GenericDecompGraph g` / `GenericBagFamily g` indexed by the node kind sum above, with `IsTree` proved from construction (not `certPathGraph7_isTree`).

---

## Lower bound scaffold (Route C, parallel track)

For tw(L(G)) = 3 **equality** (not just ≤ 3), need tw ≥ 3:

- Noncrossing core contains C₄ in suppress graph (`NoncrossingCoreIsFourCycle`); target **L(G) minor / subdivision** embedding of a width-3 obstruction (K₄ or W₃).
- Alternative: bramble of order 4 in L(G) for noncrossing instances.

Lean: add `NoncrossingLineGraphTwLowerBound` structure with `HasTreeDecomp → False` for tw ≤ 2, once explicit witness graph is chosen.

---

## Lean progress this session (2026-08-05)

| Item | Status |
|------|--------|
| `cyclicEdgeInGraph_of ∀ k` | **PROVED** (`DegreeBounds.lean`) |
| `graphEdgeSym2_mem ∀ k` | **PROVED** (`EdgeIndexing.lean`) — drops external `edgeMem` hypothesis |
| `arcConsecutive_lineGraphAdj` | **PROVED** — arc structure → L(G) adjacency |
| Generic tree T + hub placement | **DESIGN** (this doc) |
| `NoncrossingPathDecompOpenGoals` discharge | **OPEN** |
| Generic `GraphEdgeBijection` inj/surj | **OPEN** |
| tw(L(G)) ≥ 3 witness | **OPEN** |

---

## Recommended next steps

1. **Formalize node-kind sum type** in Lean (`GenericDecompNode g`) + pairing-dependent adjacency function; prove `GenericDecompGraph_isTree` without fixed Fin 7.
2. **Python/Lean search** for minimal hub placement on small (n, gaps, pairing) tuples to derive hub rules before ∀n proof.

---

## References

- `NoncrossingPathDecomp.lean` — bag definitions, open goals, c8 fork lower bound
- `EdgeIndexing.lean` — `graphEdgeSym2`, `GraphEdgeBijection`
- `ArcLengths.lean` — `cyclicGap`, arc offsets
- `notes/proofs/noncrossing_path_decomp_sketch.md` — pilot sketch
- `reports/CHORDWIDTH_PROOF_ROUTE_MATRIX.md` — route matrix
