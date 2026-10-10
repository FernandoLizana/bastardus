# Crossing short-arc tip law (beyond θ) — Category C

## Goal (G1 for crossing family)

For `G = C_n + two crossing chords`, each folded branch arc with positive
internals admits a legal deg-2 tip, so tip-by-tip multihop projection is
well-defined.

## What is already proved / mass-checked

| Layer | Status |
|-------|--------|
| θ-graph (one chord) tip ∀ residues | Lean `ThetaResidue.chordFoldLaw` |
| Crossing multihop tip-by-tip | **461/461** E2 (`multihop_projection_mass.json`) |
| Tip-kind sequences | **461/461**, **2310/2310** shortcut (`multihop_tip_kinds_mass.json`) |
| Frontier invariant (deg-2 + left deg≥3 + non-adj) | **461/461** E2 (`multihop_frontier_invariant_mass.json`) |
| Packs 1–6 hops | Lean `ProjectionInclusion` |
| 4-arc count schedule | Lean `crossing_frontier_tip_exists` |
| Open-arc path model | Lean `OpenArcPath` / `crossing_open_frontier_exists` |
| Whitney axiom interface | Lean `WhitneyEarAxiom` (`crossing_graph_embed_witness`, derived `crossing_embed_*`) |
| FoldTipElimination packs | OneFold + MultiFold×2 + FourFold hop0 |
| Outerplanar earLaw | 701/701 E2; Lean axiomatized on sketch |

## Critical observation (schedule vs θ-classifier)

Left-to-right multihop fold classifies **every** tip as `shortcut_fold`
(2310/2310). No `triangle_ear` appears.

- **Fold mode** = `frontierTipKind` / `OpenArcPath.hasFrontierTip`
- **arcTipKind** = θ bookkeeping (`internals=1` → triangleEar)

Do not equate them when writing Lean↔Python bridges.

## Graph-level content (this layer)

`OpenArcPath` records the residual open branch flags that `fold_deg2_tip`
needs: `leftDegGe3`, `endsAdjacent=false`, `internals>0`. Lean proves:

- `crossingOpenArc_frontier` — positive k ⇒ frontier tip
- `crossingOpenArc_fold_step` — fold preserves frontier-or-done
- `crossing_open_frontier_exists` — some of four arcs has a frontier tip

Still **not** a Mathlib embedding of `C_n`; the bridge from concrete cycle
indexing to `OpenArcPath` is axiomatized in `WhitneyEarAxiom.crossing_graph_embed_witness`
(with `branchOpenArc` on `CrossingEmbedWitness`; justified by E2 mass 461/461).

## Non-goals

- P vs NP
- Mathlib planar graph theory
- Packing C₁₂ full closures
