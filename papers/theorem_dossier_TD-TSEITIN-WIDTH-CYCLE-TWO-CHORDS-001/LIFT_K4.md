# Lift sketch: Crossing → K₄ width lower bound

## Goal

Show that for crossing `C_n + 2` chords with `Δ ≤ 3` and odd charge,

`Width(T(G,c)) ≥ 4 > Δ`  

by reduction to Tseitin on `K_4`, not only by saturating `G`.

## Ingredients (machine-checked)

1. **`K_4` has Width = 4 > Δ = 3`** for odd charges (unit and contracted).
2. **Crossing ⇒ K₄-minor:** four cycle-arcs between the endpoints + two chords.
3. **Charge contraction:** absorb each open-arc internal into the left endpoint
   over GF(2). On the crossing family (`n ≤ 10`), the contracted 4-tuple is odd
   (after choosing an odd-source charge when needed) and abstract `K_4` still has
   Width = 4; simultaneously `G` has Width > Δ.

Artifacts: `reports/discovery/k4_minor_crossing_law.json`,
`reports/discovery/k4_lift_charge_contraction.json`.

## Intended analytic step (open)

Path-elimination of deg-2 internals along each arc is width-≤Δ XOR Gaussian
elimination. The residual system on the four endpoints is Tseitin-on-`K_4` with
the contracted charges. Therefore:

> a width-3 resolution refutation of `G` would induce a width-3 refutation of
> that `K_4` instance,

contradicting ingredient (1).  

Making the “would induce” step precise (projection / restriction / simulation
of resolution under path contraction) is the remaining lemma for Lean or a
human write-up.

## Partial forward certificates (machine)

**Done (n≤10 crossings):** path-fold + triangle ears derive residual K₄ XOR
CNFs at width ≤ Δ for **462/462** instances, including **461** long-arc
shortcut folds (`reports/discovery/k4_path_contraction_derivation.json`,
`backend/proof_complexity/path_fold.py`).

Residual charges match GF(2) charge contraction. Width(G)=4 is certified on
sampled instances via closed width-3 saturation without □ plus empty at 4.

Still open for a fully analytic E5 proof of the inclusion for all crossings
(not merely E2 checks). See also `PROJECTION.md`.


## What is *not* claimed

This is still a resolution-width statement about Tseitin on a sparse family.
It does **not** approach Camino A/B for P vs NP.
