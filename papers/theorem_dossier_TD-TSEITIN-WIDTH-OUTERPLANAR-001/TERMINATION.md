# Outerplanar path-fold termination (Category C)

## Claim

For connected outerplanar `G` with `Δ(G)≤3` and odd charge, the procedure
`build_outerplanar_pathfold_refutation` terminates with a Width≤Δ refutation:

1. Peel trees (degree-1 tips).
2. While residual is not a cycle: fold a **triangle ear**, else a **deg-2 tip
   adjacent to a deg≥3 vertex** (shortcut / path-fold).
3. Finish the residual cycle at width 2.

## Why a fold tip always exists (2-connected case)

A 2-connected outerplanar graph that is not a cycle has at least one ear in the
classical ear-decomposition sense: a path between two vertices of the rest of
the graph whose internal vertices have degree 2. With `Δ≤3`, each ear endpoint
has degree 3 in the current residual. Hence:

- if the ear has length 2 (one internal), the tip forms a **triangle** with the
  base edge (present as a face edge in a plane outer embedding), or after prior
  shortcut folds the base is present;
- if the ear is longer, an internal adjacent to an endpoint is a deg-2 tip
  neighboring a deg≥3 vertex — exactly the shortcut case.

Thus the search in step 2 cannot get stuck while the residual stays
2-connected, outerplanar, and not a cycle.

## With pending trees

Tree pendants are removed in step 1; the claim applies to the 2-core (which
remains outerplanar, Δ≤3).

## Machine evidence

`reports/discovery/outerplanar_pathfold_certificates.json` — 130/130 certificates
on C_n+noncrossing ears and triangle chains. Broad Width=Δ hunts found no
counterexamples among checked Δ≤3 outerplanar samples.

## Gap for E5

Make the ear-existence argument fully formal in Lean (or a human write-up with
citations to outerplanar ear decompositions) and prove that each fold preserves
outerplanarity / Δ≤3 / odd charge. The Python certificates already implement
the inductive step on certified instances.

Lean scaffold: `lean/PNPLab/Outerplanar.lean` — `ResidualSketch` + `earLaw`
hypothesis + fold measure / `foldsExhaust` termination skeleton +
`classify_coherent` / concrete C₄ triangle residual lemmas (not yet a
graph-theoretic ear theorem).

Lean addendum: `lean/PNPLab/OuterplanarUpperSketch.lean` packages the formal
measure-level induction:

- `upperFoldStep_exists`: non-cycle + positive measure ⇒ tip kind + strict drop.
- `upperFoldStep_status`: classifier status, concrete tip, and drop in one bundle.
- `outerplanar_measure_induction`: reusable induction over vertex budget.

This closes the sketch-level termination/measure part of G6. It still assumes
the graph-theoretic ingredients: `earLaw`, fold preservation of outerplanarity,
`Δ≤3`, and charge invariants.

Lean addendum (total elimination): `lean/PNPLab/OuterplanarFoldTermination.lean`
turns the single-fold measure into a **total, terminating fold-to-base**:

- `foldSucc`: deterministic successor (drops one vertex on any non-base sketch,
  fixpoint on cycle/degenerate base); `foldSucc_lt` gives the strict drop.
- `foldNormal` / `foldSteps`: well-founded recursion to the base and its fold
  count.
- `foldNormal_atBase`: the normal form is always a base (cycle or 0 vertices).
- `foldSteps_le`: the number of folds is bounded by the vertex count
  (`foldSteps_base`, `foldSteps_pos`, `foldSteps_cycle`, `foldSteps_c4_le`).

This makes the ear-peeling induction a genuine terminating recursion with a
proven step bound, not just a per-step measure drop. Facial triangle cores
close in one step via `OuterplanarFacialInduction`
(`reaches_cycle_base`: cycle embed + odd charge + `foldSteps = 0`). Multi-chord
nested diagrams need two facial steps: ear fold leaves
`residualOuterChord` (`NestedChordResidual` / `NestedTriangleInduction`; C₈
mid ≠ cycle, final = cycle). Disjoint diagrams similarly leave
`residualSecondChord` (`DisjointChordResidual`). Whitney
ear *existence* on general 2-cores is now isolated by
`lean/PNPLab/OuterplanarBlockCut.lean`: its certificate records a rooted
block-cut tree, valid articulation vertices, and local ears for non-cycle
2-connected blocks. Strictly decreasing parent indices prove that the maximal
block is a leaf. The public API is now data-valued:
`OuterplanarCoreExposure` (`cycleBase` | sized legal `ear`) via
`OuterplanarBlockCut.expose` / `legalEarOfNotCycleBase` — computational, with
no `Classical.choose`. Size coherence (`nonCycleEarFits`, `blockSize_le_core`,
`singleBlock_size`) keeps exposed ears strictly under the fold measure.
`upper_step` connects the residual bridge to the classifier/fold layer.
`twoCycleBlockCore` and `c4TriangleBlockCore` check articulation and single-block
cases concretely.

For the actual Δ≤3 theorem, `SubcubicOuterplanarBlockCut.nBlocks_eq_one` is
stronger: two nontrivial blocks meeting at an articulation each contribute at
least two incident edges, contradicting the degree-three budget. Hence a
subcubic 2-core has exactly one block, and `rootLegalEar` reduces the proof to
the 2-connected case.

The remaining graph-theoretic obligation is therefore narrower: construct the
unique block certificate and its local ear from a `SimpleGraph` plus an
outerplanar embedding. Mathlib v4.32.0 has no `IsOuterplanar`, so the project
does not claim that extraction theorem yet.

E2 addendum: `outerplanar_full_closure_mass.json` — **57/57** noncrossing
C_n+2 (Δ≤3) have □ ∈ full Closure_Δ.

E2 earLaw content: `outerplanar_ear_existence_mass.json` — **701/701** (n≤14;
`outerplanar_ear_existence_mass_n14.json`). Outline: `EAR_LAW_OUTLINE.md`.
sampled outerplanar Δ≤3 cores (after tree peel) are either cycles or have a
triangle ear / shortcut tip. `ResidualSketch` still accepts `earLaw` as a
field, but `OuterplanarBlockCut.upper_step` now discharges it for any supplied
block-cut certificate; θ-graph tip law is discharged in `ThetaChordFold.lean`.
