# E4 sketch: Width = Δ for bicyclic Δ≤3 (Category C)

## Statement

Let `G` be connected with cyclomatic number γ=2 (bicyclic), `Δ(G)≤3`, and
`c` an odd charge. Then `Width(T(G,c)) = Δ(G)`.

## Proof outline (machine-certified derivation)

1. **Peel trees** attached to the 2-core (Unit–XOR / leaf induction), preserving
   odd total charge and never exceeding width Δ.
2. The 2-core is `C_k` plus one chord (θ-graph).
3. **Path-fold** the shorter chord-arc: eliminate deg-2 internals by XOR-sum on
   the tip edge, rebinding the surviving edge variable as a shortcut when the
   two neighbors are not already adjacent (`path_fold.py`).
4. When a **triangle ear** appears, absorb the tip charge into one endpoint and
   derive residual endpoint XOR CNFs by targeted width-Δ saturation.
5. The residual is a **cycle**; finish by width-2 saturation (cycle lemma).

## Evidence

- Constructive: `prove_bicyclic_pathfold_lemma` (arbitrary chord length).
- Mass check: `reports/discovery/bicyclic_pathfold_mass.json` (**77/77** for n≤9);
  also `pathfold_certificates.json` (same count historically).
- Prior peel+Δ-sat certificates remain as a coarser upper-bound method.

## Status

E4-style certificate + E2 mass support. Lean:
- scaffold `Bicyclic.lean` (`chordFoldLaw` field on sketches);
- **`ThetaChordFold.lean`**: proves `ThetaResidue.chordFoldLaw` for *all*
  cycle+chord residues (triangle vs shortcut by short-arc internals);
- upper-bound packs `BicyclicWidth3` / `BicyclicC5Width3` / `BicyclicC6Width3`;
- mass `bicyclic_full_closure_mass.json` (**48/48** n≤12);
- induction plan: `INDUCTION_WIDTH_EQ_DELTA.md` + `induction_shape_bundle`.
Full inductive Width=Δ for every bicyclic graph still open. Not P vs NP.
Pathfold mass: **210/210** n≤12 (`bicyclic_pathfold_mass.json`).
Lean bridge: `ThetaFoldBridge` (C₆ tip + `bi6_has_empty`).
E5 gaps: `papers/E5_GAPS_CHECKLIST.md`.
