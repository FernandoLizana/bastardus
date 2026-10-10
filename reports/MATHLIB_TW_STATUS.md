# Mathlib treewidth API status (PR #38334)

**Checked:** 2026-08-03  
**Context:** ChordWidth Phase 4 gate — see [CHORDWIDTH_INTEGRATION_SUMMARY.md](CHORDWIDTH_INTEGRATION_SUMMARY.md), [COMMUNITY_QUESTION_DRAFT.md](COMMUNITY_QUESTION_DRAFT.md).

---

As of **August 2026**, Mathlib4 PR [#38334](https://github.com/leanprover-community/mathlib4/pull/38334) (*feat(Combinatorics/SimpleGraph/TreeDecomp): define tree decompositions*, author 8e7, assignee YaelDillies) remains **open and unmerged**. Opened 2026-04-21; last activity 2026-07-26. The PR adds `Mathlib.Combinatorics.SimpleGraph.TreeDecomp` with `TreeDecomp`, `HasTreeDecomp`, `SimpleGraph.treeWidth`, and ~73 supporting lemmas (monotonicity, embedding, trivial decompositions, etc.). Its dependency #38027 (star graphs) has merged; the PR is on the review queue with reviewer feedback on generalizing to pathwidth before merge — the author proposed either a generic `GraphDecomposition` base or `PathDecomp` as a subtype of `TreeDecomp`. Follow-up PR [#39939](https://github.com/leanprover-community/mathlib4/pull/39939) (clique lemma: tw(K_n) = n−1, hence `cliqueNum − 1 ≤ treeWidth`) depends on #38334 and is also open. **Implication for ChordWidth:** v4.32.0 (current pin) still has no `SimpleGraph.treeWidth`; upgrading the pin today does not unlock treewidth unless tracking #38334’s branch or waiting for merge. Local `EliminationOrder` / `TreewidthWitness` stubs remain the practical path until #38334 lands.
