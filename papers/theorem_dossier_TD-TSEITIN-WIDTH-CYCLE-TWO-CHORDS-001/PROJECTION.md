# Projection / restriction support (G → residual K₄)

## Analytic statement

After path-folding open arcs of a crossing `C_n+2` instance to a residual `K₄`
edge-variable set `V_res`, let:

- `Closure₃(G)` = width-3 resolution closure of Tseitin(`G`);
- `Closure₃(R)` = width-3 closure of the residual vertex-XOR axioms on `V_res`.

**Restriction claim:**  
`{ C ∈ Closure₃(G) : vars(C) ⊆ V_res } ⊆ Closure₃(R)`.

Then `□ ∈ Closure₃(G)` implies `□ ∈ Closure₃(R)`. Combined with
`Width(K₄)=4` (so `□ ∉ Closure₃(R)` for odd residual charge), one obtains
`Width(G) ≥ 4` without needing a separate “hand” argument for each `G` —
provided the inclusion is proved for the family, not only checked.

## Machine evidence

Script: `backend/proof_complexity/k4_projection_restriction.py`  
Artifact: `reports/discovery/k4_projection_restriction.json`

On sampled crossings (**792/792** for `n=4..11`), the inclusion holds together with:

- forward path-fold deriving residual XORs at width ≤ Δ;
- charge match with GF(2) contraction;
- both `G` and residual `K₄` free of `□` at width 3.

## Analytic outline for the inclusion (toward E5)

Resolution is closed under taking subsets of axioms: any clause derived from
`G` using only residual variables must be derivable from the *projection* of
the axiom set onto those variables. Path-fold shows that after eliminating
arc-internal edge variables by width-≤Δ XOR sums, the projected axioms are
exactly the residual vertex XORs `R`. Hence `Closure₃(G)|_{V_res} ⊆ Closure₃(R)`.

The remaining formality is to present path-fold as a sequence of
variable-elimination steps that each preserve the width-3 closure projection
property (standard for Gaussian elimination on XOR systems / unit-XOR style
reasoning), which is what Lean should capture.
