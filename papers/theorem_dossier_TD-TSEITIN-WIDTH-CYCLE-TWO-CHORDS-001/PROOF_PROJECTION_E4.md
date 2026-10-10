# E4 outline: Projection / restriction for crossing Cₙ+2 ⇒ Width ≥ 4

## Theorem (Category C)

Let `G = C_n` plus two crossing chords with four distinct endpoints, `Δ(G)≤3`,
and odd charge `c`. Then `Width(T(G,c)) ≥ 4`.

## Proof outline

### Step A — Path-fold (machine certificate)

Along each of the four open arcs between the chord endpoints, eliminate deg-2
internals by width-≤Δ XOR-sum / triangle-ear / shortcut fold
(`path_fold.py`, `k4_path_contraction_derivation.py`).

**Output:** residual Tseitin axioms `R` on an edge-variable set `V_res` of a
`K₄` on the four endpoints, with residual charges matching GF(2) charge
contraction. Certificate: 462/462 crossings.

### Step B — Restriction lemma (analytic)

Let `Closure_w(·)` be width-`w` resolution closure.

**Claim.** For `w = 3`,
`{ C ∈ Closure_w(T(G,c)) : vars(C) ⊆ V_res } ⊆ Closure_w(R)`.

*Reasoning.* Each path-fold step is a variable-elimination / XOR-Gaussian step
whose derived clauses of width ≤`w` supported on the surviving variables are
exactly those obtained from the residual XOR system after elimination. By
induction on the number of eliminated internals, any width-`w` derivation from
`G` whose final clause uses only `V_res` factors through `R`.

(Lean: `PNPLab.Resolution.no_empty_of_projection` + `EliminationStep` /
`EliminationChain` in `ResolutionClosure.lean`; concrete non-identity tip
instance in `TipElimination.lean`; **real XOR triangle**
`triProjection` / `triEliminationChain` in `TriangleProjection.lean`
(residual `triRPool`); **n=5 one-fold** `ofoldProjection` in
`OneFoldProjection.lean` (42→16); **n=6 two-arc** `mfEliminationChain` in
`MultiFoldProjection.lean` (68→42→16); **n=6 length-2 arc tip-by-tip**
`laEliminationChain` in `LongArcProjection.lean` (92→42→16);
**n=7 three-tip** `tfEliminationChain` / `composeProjection3` in
`TripleFoldProjection.lean` (118→68→42→16);
**n=8 four-tip** `ffEliminationChain` / `composeProjection4` in
`FourFoldProjection.lean` (168→118→92→42→16);
**n=9 five-tip** `xfEliminationChain` / `composeProjection5` in
`FiveFoldProjection.lean` (248→168→118→92→42→16).
E2: direct projection 792/792; **multihop tip-by-tip 461/461**;
bicyclic full Closure_Δ∋□ **15/15**; outerplanar noncrossing **57/57**.
)

### Step C — K₄ lower bound

Odd-charge Tseitin on `K₄` has Width = 4 (exact width oracle / certificate):
`□ ∉ Closure_3(R)` and `□ ∈ Closure_4(R)`.

Lean pack: `lean/PNPLab/K4Width3.lean` — `k4Closure : WidthClosure 3` with
the 16 ternary XOR axioms, `k4_no_empty`, and `k4SelfProjection`.
Same residual shape appears as `ofoldRClosure` / `mfRClosure` / `laRClosure`.

### Step D — Conclusion

If `□ ∈ Closure_3(T(G,c))`, Step B puts `□ ∈ Closure_3(R)`, contradicting Step C.
Hence `Width(T(G,c)) ≥ 4 > Δ`.

## Status

- A, C: machine-certified.
- B: E2 multihop 461/461 + Lean instance packs (one-fold / two-arc / long-arc);
  Lean `composeProjection` glues two hops when `Vres ⊆ V₁`;
  **family-level Lean** multihop preservation still open.
- Not P vs NP.
