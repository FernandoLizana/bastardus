# E4 sketch: Noncrossing C_n+2 chords ⇒ Width = Δ

## Statement

If `G = C_n` plus two noncrossing chords with four distinct endpoints,
`Δ(G)≤3`, and `c` odd, then `Width(T(G,c)) = Δ(G)`.

## Proof outline

1. Peel pendant trees.
2. Repeatedly: clip **triangle ears**; else **path-fold** one deg-2 tip on a
   chord’s shorter arc (shortcut rebinding). Nested chords are handled by
   ear-first ordering.
3. Residual cycle → width-2 finish.

Crossing case is the complementary lower bound (K₄ path-fold + Width(K₄)=4;
projection lemma still the analytic gap for a sat-free lift — see `LIFT_K4.md`).

## Evidence

- `prove_noncrossing_pathfold_lemma`
- `reports/discovery/pathfold_certificates.json` (57/57 noncrossing n≤8)
- Crossing forward residual: `k4_path_contraction_derivation.json` (462/462)

## Status

E4 sketch + E2 certificates. Lean E5 open. Not P vs NP.
