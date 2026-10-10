# XOR ear-clip modes (Category C)

## Bare triangle (`Ou=Ow=[]`)

Odd face charge ⇒ after `eq_u ⊕ eq_v` on the tip edge, `mid` and `eq_w` are
contradictory XORs on `{y,z}`. Resolution of those two XOR CNFs yields □
(`mode=pure_xor_empty`). Demo in `xor_resolution.demo_triangle_ear_xor`.

## One empty stub side

- `Ow=[]` and `χ_w=0`: `mid ⊕ eq_w` on `y` derives `residual_u = XOR({z}∪Ou)=α`
  by pivot-sum alone.
- `Ou=[]` and `α=0`: symmetric for `residual_w`.

## Both stub sides nonempty (typical `C_n`+length-2 chord)

Pivot-sums still produce the elimination identities, but splitting into
*separate* residual endpoint XORs is not a propositional consequence of a
single XOR-sum (existential elimination of the tip edge). Certificates use
`fill_xor_by_local_sat` / `_saturate_until_targets` for those residual CNFs.

Mass check: `reports/discovery/xor_ear_modes.json` — 39/39 length-2 ears
on `n=4..9` finish under that hybrid; 0 failures after sum-or-target fallback.

**Gaussian / local-only attempt** (`xor_gaussian_residual_split.py` →
`xor_gaussian_residual_split.json`): after tip XOR-sum, filling residual_u /
residual_w using *only* residual variables fails on C₆+length-2 (`gap_remains`).
Mass confirmation: **45/45** n=5..10 (`xor_gaussian_gap_mass.json`); see
`XOR_GAP_STATUS.md`.
Bridge clauses from the rest of the Tseitin are required — remaining analytic
gap toward a sat-free CNF Gaussian elim.

## Status

Pure-XOR □ for isolated triangles is settled. General outer stubs remain
hybrid (XOR-sum + local/targeted residual sat), matching the path-fold certificates.

**Obstruction witness** (`reports/discovery/xor_both_stubs_obstruction.json`):
on `C_6`+chord length-2 with both `Ou, Ow` nonempty, pivot XOR-sums alone do
**not** place the separate residual endpoint CNFs. `clip_triangle_ear_xor`
prefers `fill_xor_by_local_sat` (`mode=local_xor_residuals`); if that fails it
falls back to builder-global target-sat.
