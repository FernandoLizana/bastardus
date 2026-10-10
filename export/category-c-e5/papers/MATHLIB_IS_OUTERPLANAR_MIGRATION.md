# Mathlib `SimpleGraph.IsOuterplanar` — migration notes (E5 item 3)

**Status:** **scaffold complete, upstream blocked** (PNPLab work closed; blocked solely on Mathlib upstream API)

Mathlib pin: **v4.32.0** (`lean/lakefile.toml` rev `v4.32.0`; `lean/lean-toolchain` `leanprover/lean4:v4.32.0`).

Lean module: `lean/PNPLab/MathlibBridge.lean` — builds green as part of `lake build PNPLab`.

## Upstream verification (2026-07-30, re-confirmed)

From `lean/` (Mathlib package at `.lake/packages/mathlib`):

```powershell
# SimpleGraph tree — 88 .lean files
rg -l "IsOuterplanar|outerplanar" .lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph
# → 0 files

rg -l "IsPlanar|PlanarGraph|Kuratowski|treewidth|TreeWidth" .lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph
# → 0 files

rg -l "IsOuterplanar|outerplanar" .lake/packages/mathlib/Mathlib
# → 0 files
```

Grep over `.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph` (**88** `.lean` files) and full `Mathlib/`:

| Symbol | Present in v4.32.0? |
|--------|---------------------|
| `IsOuterplanar` / `outerplanar` | **No** |
| `IsPlanar` / `PlanarGraph` | **No** |
| graph-minor `Kuratowski` | **No** |
| `treewidth` / `TreeWidth` | **No** |

Lean record: `PNPLab.MathlibBridge.MathlibIsOuterplanarAbsent`, `MathlibIsOuterplanarSearch`.

## PNPLab scaffold (complete)

Module: `lean/PNPLab/MathlibBridge.lean`.

| Layer | Artefact | Role |
|-------|----------|------|
| Local stand-in | `IsOuterplanar` ≃ `IsFacialOuterplanar` | Honest project predicate (not Mathlib geometry) |
| Export bundle | `OuterplanarExportCert` | facial + local + embed + `OuterplanarGraphInstance` + `toSimpleGraph` |
| Roundtrips | `MathlibIsOuterplanarGap` | facial ↔ export ↔ local; graph embed roundtrip |
| Absence | `MathlibIsOuterplanarAbsent` / `Search` / `Anchors` | documented grep + peel anchors (IsTree, cycleGraph, pathGraph) |
| Peel hooks | `facialCycleBase_toExportCert`, `CycleChord.reaches_cycle_export`, `mass_window_one_chord_export_chain` | facial proofs → export certs |
| Mass window | `mass_window_upper_bound_export_facial`, `smoke_endpoint_cycle_export` | ∀ `CrossingEndpoints` with 5≤n≤14 |
| Smoke seeds | `canonical_smoke_export_certs` | 7 canonical n=5..10 emit-backed endpoints |
| Migration hook | `MathlibIsOuterplanarUpstreamHook` | `True`-typed placeholders for upstream obligations |
| Bundle | `mathlibOuterplanarBridgeBundle` | single import surface for downstream |

## Blocked on upstream

Once Mathlib ships `SimpleGraph.IsOuterplanar` (expected module e.g. `Mathlib.Combinatorics.SimpleGraph.Outerplanar`):

1. Import upstream module; extend `MathlibIsOuterplanarSearch.anchorModules`.
2. Replace `MathlibIsOuterplanarUpstreamHook.export_to_mathlib : True` with
   `OuterplanarExportCert n → IsOuterplanar (exp.graph.toSimpleGraph)` (Mathlib sense).
3. Prove alignment on cycle / one-chord cores: PNPLab `IsOuterplanar` ↔ Mathlib on `cycleGraph` / `CycleChord.toSimpleGraph`.
4. Chain peel induction via existing hooks + Mathlib tree lemmas (`IsTree.exists_vert_degree_one_of_nontrivial`).

## Checklist cross-links

- `papers/E5_GAPS_CHECKLIST.md` — item 3 (Mathlib export bridge; ~~strikethrough~~ closed on PNPLab side)
- `papers/REMAINING_CHECKLIST.md` — **Blocked** section (upstream Mathlib API)
- `papers/FAMILY_PROJECTION_E5.md` — Category C projection layer
- `papers/QUEUE_AUTONOMOUS.md` — G5/G6 upstream blocked

## PNPLab closure (2026-07-30)

All PNPLab-side obligations for E5 item 3 are discharged:

- Local predicate + equivalence (`IsFacialOuterplanar.lean`, `isOuterplanarEquivIsFacialOuterplanar`)
- Export certificate bundle + roundtrips (`OuterplanarExportCert`, `MathlibIsOuterplanarGap`)
- Absence records + migration anchors (`MathlibIsOuterplanarAbsent`/`Search`/`Anchors`)
- Peel and mass-window hooks wired to facial proofs
- Seven canonical smoke export certificates (`canonical_smoke_export_certs`)
- Upstream hook placeholders reserved (`MathlibIsOuterplanarUpstreamHook`, `mathlibOuterplanarBridgeBundle`)

**Remaining work is exclusively upstream:** Mathlib must ship `SimpleGraph.IsOuterplanar` before the `True`-typed hook fields can be replaced with real Mathlib implications.

## What we do **not** claim

- Geometric outerplanarity in Mathlib sense (predicate absent).
- Ear-decomposition / Whitney block-cut from Mathlib (see `WhitneyEarAxiom`, `OuterplanarBlockCut`).
- Full E5 completion (combinatorial `parametricDischargeCombinatorialForAll` remains open separately).
