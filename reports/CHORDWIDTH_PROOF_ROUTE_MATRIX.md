# ChordWidth Proof Route Matrix

**Date:** 2026-08-04 | **Selected route:** **F → A** (path decomposition on cyclic arcs)

| Ruta | Cota superior | Cota inferior | Formalización Lean | Riesgo | Estado |
|------|--------------:|--------------:|-------------------:|-------:|--------|
| **A** Descomposición explícita L(G) | tw≤3/4 | needs C | Media | Generic typed tree T | **REDESIGN** ([CHORDWIDTH_GENERIC_DECOMP_DESIGN.md](CHORDWIDTH_GENERIC_DECOMP_DESIGN.md)) |
| **B** Subdivisión ↔ L(H') | unknown | unknown | Baja | Effect on line graph unclear | OPEN |
| **C** Menores / brambles | — | tw≥3/4 | Media-Alta | Need explicit minor in L(G) | OPEN |
| **D** Núcleo K4/C4 suppress | via core | via core | Media | isK4 not iso; L(G) gap | PARTIAL (smokes) |
| **E** Outerplanaridad | maybe tw≤3 | weak | Baja | L(G) not outerplanar in general | OPEN |
| **F** Path decomposition | pw≤3/4 ⇒ tw≤ | same as C | **Alta** | Linear arc structure | **SELECTED** |
| **G** Literature (Harvey–Wood) | inequalities | — | Baja | Need exact match to family | RESEARCH |

---

## Selection rationale

1. **Noncrossing first:** four positive cyclic gaps (`ArcLengths.lean`) give natural linear bag order along C_n.
2. **Pathwidth sufficient:** `tw ≤ pw`; explicit path of bags avoids running-intersection engineering on general trees.
3. **Avoid premature K4 route:** G2 `isK4` is combinatorial on suppress-graph, not proven equivalent to tw(L(G))=4 ∀n.

---

## Immediate lemma chain (noncrossing upper bound)

1. ✅ `cyclicGaps_sum` — four arc lengths partition n (**PROVED**)
2. ✅ Stable edge labeling `Fin (n+2)` — `EdgeIndexing.lean` (`graphEdgeSym2`, `GraphEdgeBijection`, `lineGraphVertex`)
3. ✅ Route F+A block 1 — long-arc sliding bags, width ≤ 3 (**PROVED**)
4. ✅ Route F+A block 2 — chord-junction bags, L(G) bag mapping, local edgeCover on arc pairs (**PROVED**)
5. ✅ Route F+A block 3 — `LongArcSegmentFragment`, junction glue at chord1 start, open-goals checklist (**PROVED** scaffold)
6. ✅ Route F+A block 4 — c8 arc preconnected, junction glue 4/4, `globalBagFamily` (**PROVED**)
7. ✅ Route F+A block 5 — short-arc bags, `globalDecompGraph`, `globalTreeDecomp` + open-goals builder (**CONDITIONAL**)
8. ⚠️ c8 Route F+A discharge — **path + 7-node fork infeasible** at width ≤4 (junc₁ hub needs ≥6 edges); parked
9. ✅ Generic lemmas — `cyclicEdgeInGraph_of`, `graphEdgeSym2_mem`, `arcConsecutive_lineGraphAdj` (**PROVED**)
10. ✅ `GenericDecompNode`, `genericDecompAdj`, `genericBagFamily`, width ≤3 (**PROVED**)
11. ✅ `graphEdgeSym2_injective` + **`graphEdgeSym2_surj`** + `graphEdgeBijection` (**PROVED**)
12. ✅ `genericBagFamily_width_le_sup`, `genericTreeDecomp`, `genericConditionalHasTreeDecomp_of_cert` (**PROVED** conditional)
13. ✅ GenericDecomp recovered + OpenGoals scaffold (`isTree_of_combinatorialCard`, cover fragments) (**PROVED** partial)
14. ✅ `genericDecompNodeFinEquiv`, `mkGenericDecompFinTransport`, `genericDecompNodeCount_eq_card` (**PROVED**)
15. ✅ Fin transport + `genericConditionalHasTreeDecomp_of_openGoals` + shortSeg preconnected (**PROVED**)
16. ⚠️ **`edgeCard` Fin bijection** — **OPEN** (optional; Route B closed without it)
17. ✅ ALT route wired (**PROVED**)
18. ✅ **Route B CLOSED** — `tagOfEdge`, `card_edgeSet_le_edgeCount`, **`GenericDecompOpenGoals.isTree_of_shape`** (**PROVED** via `byCases` helper defs, subagent ca85ebf9)
19. ✅ **`longArc_edgeCover` CLOSED** — EdgeIndexing + NCP + `of_noncrossingLineGraphBag` (**PROVED**, subagent 584f531c)
20. ✅ **c8 GenericDecomp cert CLOSED (extended)** — `C8ExtendedOpenGoals` + `genericConditionalHasTreeDecomp_c8NestedGraph` **PROVED** (subagent 025c58dc); standard-adj `GenericDecompOpenGoals` preconnected **OPEN** (6/10 blocked); c8 tw=3 also via CertificatesLine

---

## Crossing branch

After noncrossing pilot: expect bags of size ≤ 5 (width ≤ 4). Likely needs different junction pattern (K4-type core near crossing).

---

## Abandoned for now

- **Full Mathlib treeWidth upgrade** — blocked on PR #38334; continue with vendored `HasTreeDecomp`.
- **More smoke certificates** — does not close universal gap.

---

## Next exact action

**Next:** parametric ∀n discharge; optional Laws wire for `genericConditionalHasTreeDecomp_c8NestedGraph`; crossing branch / G2 / G5.

| Topology | Result |
|----------|--------|
| 6-node path | k=5,k=6 non-interval |
| 7-node path | 0 interval solutions (search 7–10 nodes) |
| 7-node fork (junc₁ hub) | `IsTree` proved; preconnected **fails** — hub needs card 6 → width 5 |

**Alternatives:** (a) 8+ node split hub, (b) populate bridge/trim bags, (c) c8 tw=3 via `CertificatesLine` (already **PROVED**) while keeping Route F+A as parametric scaffold.

**Parametric ∀n:** still **OPEN** — needs topology beyond fixed 7-node templates.
