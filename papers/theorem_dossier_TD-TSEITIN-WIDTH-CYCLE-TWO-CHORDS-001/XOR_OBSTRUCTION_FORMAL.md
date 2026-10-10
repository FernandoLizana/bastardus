# XOR both-stub obstruction — formal note (Category C, optional)

## Claim (combinatorial)

On a length-2 triangle ear `u—v—w` with **both** stubs nonempty
(`Ou = incident(u) \ {uv}`, `Ow = incident(w) \ {vw}` nonempty), the two
endpoint residual XORs

- `residual_u`: XOR on `Ou ∪ {uw?}` with charge χ_u ⊕ χ_v (or equivalent)
- `residual_w`: similarly at `w`

are **not** consequences of iterating only the local pivot sums
`eq_u ⊕ eq_v` and `eq_w ⊕ eq_v` inside the tip support
`{uv, vw} ∪ Ou ∪ Ow`.

Bridge variables outside that local cut are required for a pure Gaussian
completion — or else a hybrid clip (`clip_triangle_ear_xor` + target-sat).

## Evidence

| Layer | Result |
|-------|--------|
| Witness | `xor_both_stubs_obstruction.json` — pure XOR-sums fail to place both residuals |
| Mass | `xor_gaussian_gap_mass.json` — **45/45** `gap_remains` (n=5..10) |
| Hybrid OK | `xor_ear_modes.json` — **39/39** hybrid clip succeeds |
| Lean | `XorObstruction`: GF(2) masks + C₆ mid/tip 2-span does not place both residuals |

## Why this does not block Width=Δ / crossing law

Upper bounds use **path-fold + width-Δ saturation**, not pure local Gaussian
fill. Lower bounds use **ProjectionInclusion / EliminationStep** on stop-at-□
closures. Closing the XOR gap would be a nicer algebraic lemma, not a
prerequisite for G1–G6 / G8.

## Non-goals

- Proving P≠NP via XOR algebra
- Replacing path-fold with Gaussian elimination in Lean packs

## Status

- [x] E2 systematic gap documented
- [x] This formal obstruction statement (combinatorial)
- [x] Lean GF(2) Nat bookkeeping (`gf2Add`, residual supports, C₆ overlap-only-z)
- [x] Lean finitary GF(2) masks / 2-span obstruction (`c6_gf2_obstruction_bundle`)
- [x] Lean 3-span extension (`c6_gf2_span3_bundle`)
- [ ] Lean full matrix Gaussian over arbitrary supports (optional, low priority)
