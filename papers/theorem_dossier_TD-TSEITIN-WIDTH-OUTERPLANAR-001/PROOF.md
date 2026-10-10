# Sketch: Outerplanar Δ≤3 ⇒ Width = Δ (Category C)

## Statement

If `G` is connected outerplanar, `Δ(G)≤3`, and `c` is odd, then
`Width(T(G,c)) = Δ(G)`.

## Intended induction

Outerplanar graphs with `n≥3` have an **ear**: a deg-2 tip `v` whose neighbors
`u,w` are adjacent (triangle face) — or, after tree-peel, a cycle with
noncrossing chords admitting path-folds as in `path_fold.py`.

1. Peel pendant trees (Width ≤ Δ), as in the tree lemma.
2. While a triangle ear exists: fold tip into an endpoint at width ≤ Δ
   (targeted residual XOR derivation).
3. While a noncrossing chord has a longer open arc: shortcut-fold one
   deg-2 internal (same mechanism).
4. Residual is a cycle ⇒ Width = 2 ≤ Δ.

Base: trees / cycles already proved. Crossing configurations are excluded by
outerplanarity.

## Evidence

- Constructive certificates: `prove_outerplanar_pathfold_lemma`
  (`reports/discovery/outerplanar_pathfold_certificates.json` — 130/130 on
  ear families + triangle chains).
- E2 searches: `outerplanar_width_eq_delta*.json` (no Width>Δ among checked
  Δ≤3 outerplanar samples).

## Status

Constructive algorithm + certificates on outerplanar C_n+ears / triangle
cacti with Δ≤3. Full induction over *all* outerplanar Δ≤3 graphs still
requires arguing that the fold heuristic always reaches a cycle (true for
2-connected outerplanar by ear decomposition; trees already peeled).
Not P vs NP.
