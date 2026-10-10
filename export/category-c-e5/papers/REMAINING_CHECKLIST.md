# Remaining work checklist

Last updated: 2026-07-30 (`lake build PNPLab` green — 1368 jobs; Part2+Part3 + post-Cursor recovery).

## Done (Category C / Width vs Δ)

| Item | Status |
|------|--------|
| **Parametric discharge catalog (461 emit)** | **OK** `ParametricDischargePart1/2/3` + `ParametricDischargeAll` |
| **E2 parametric projection mass** | **461/461** Python + `ParametricProjectionMass` |
| **`topologyPermForEndpoints` / 10-class lookup** | **OK** `CrossingTopologyPermLookup` + `globalTopologyRenameFor` + `topologyPermForCatalogIndex` |
| **`topologyPermForArcs` partial (83/461)** | **OK** `topologyPermArcShapeUnique`, mass 209/83/126; c5Alt1 arcs-unique, c5Ofold/c6 ambiguous |
| **`topologyPermForArcsP0` partial (461/461)** | **OK** `(n,toArcs,p0)` minimal partial key; c5Ofold/c6 smoke; `topologyPermArcsP0EndpointAgreementFlags_mass`; Vres collision documented (`c6Endpoints0234`/`1345`, 459/461); **sin forma cerrada combinatoria** (`topologyPermNoClosedFormDoc`) |
| **Mathlib export bridge** | **OK scaffold, upstream blocked** | `OuterplanarExportCert`, peel→`cycleGraph`; `isOuterplanarEquivIsFacialOuterplanar`; `IsFacialOuterplanar.fromExport`; `MathlibIsOuterplanarAbsent`/`Search`/`Anchors`; peel hooks; `canonical_smoke_export_certs`; `mathlibOuterplanarBridgeBundle`; `MATHLIB_IS_OUTERPLANAR_MIGRATION.md` |
| **Prop combinatorial bridge** | **OK** `closureFromSaturated`, `parametricProjHolds`, `ParametricCombinatorialBridge` |
| **Combinatorial discharge gap (E5 open 1)** | **Parcial** `ParametricCombinatorialDischarge`: `ForAll↔Witnesses`; explicit `WitnessesForAll`/`SufficientForAll`/`ArcP0Catalog`/`ArcUniqueCatalog` subclasses + hierarchy from ForAll; `parametricDischargeReducesToArcP0`/`ArcUnique` + `ParametricArcP0GoalSufficient`; saturate→`WidthClosure`; perm-agrees rename; mass-window ceiling (`c8EndpointsEven` vs `c8Endpoints0123`: same hop, projOK=true, discharge only canonical); canonical 7/461 smoke; emit 461/461 contrast |
| **Master discharge ⇒ FreshG0** | **OK** `parametric_discharge_fresh_g0` + catalog mass link (461 flags) |
| **Canonical + API `ParametricEndpointsDischarge`** | **OK** |
| `lake build PNPLab` | **OK** (1368 jobs, 2026-07-30 ~13:08 local; ~3.2 h; warnings defProp only) |

## Still open (honest remainder)

1. **Combinatorial discharge without emit** — `ForAll↔Witnesses` **OK** (blocker = per-instance saturate Bool checks, not topology perm); explicit subclasses **OK** (`WitnessesForAll`, `SufficientForAll`, `ArcP0Catalog`, `ArcUniqueCatalog`, fixed-n/range/mass-window + ForAll⇒subclass hierarchy); perm rename + `ParametricCombinatorialGoalSufficient` **OK**; reduces to `ParametricArcP0GoalSufficient` when `parametricDischargeReducesToArcP0` (461/461 catalog tabulation); to arc-unique when `parametricDischargeReducesToArcUnique` (83/461); mass-window hop precond necessary not sufficient **OK** (`c8EndpointsEven` vs `c8Endpoints0123`: same hop, `projOK=true`, discharge only for canonical seed); canonical 7 smoke partial **OK** (emit-backed); **no** combinatorial `parametricDischargeCombinatorialForAll` without emit/native_decide per instance. **Ceiling:** 461 discharge flags, 461 topology flags, 461 arc_p0 agreement — all emit-checked, not Prop-derived.
2. **Perm dst without full endpoint key** — **Cerrado (honesto, catálogo)** — 461-key hash OK (`topologyPermForEndpoints`); partial `(n, toArcs)` OK for **83/461**; **minimal partial `(n, toArcs, p0)` OK for 461/461** (`topologyPermForArcsP0Of`, agrees with full hash); `(n, toArcs, p1)` also 461/461 (redundant with p0+arcs); cyclic norm **0/461**; `(n, arcs, Vres)` **459/461** (sole collision: n=6 arcs=(1,0,0,1), Vres=[2,4,5,6,7,8], idx 10/18 — Lean `topologyPermArcsVresCollision_*`). **Sin forma cerrada combinatoria sin emit/tabulación** — perm = iso E2; 126/209 formas multi-perm; invariantes schedule+ p0 insuficientes; ver `topologyPermNoClosedFormDoc`, `closed_form_verdict` en `topology_perm_arcs_analysis.json`. Puente Lean: `ParametricArcP0GoalSufficient`, `parametricTopologyPermPartialKey_mass`.

## Blocked

Camino A/B P vs NP — claim-gate `may_present=False`.

**Mathlib `SimpleGraph.IsOuterplanar`** — **scaffold complete, upstream blocked** (E5 item 3 closed on PNPLab side, 2026-07-30). Mathlib v4.32.0 re-verified: 88 `SimpleGraph` files + full Mathlib — 0 matches for outerplanar/planar/Kuratowski/treewidth. PNPLab bridge complete in `MathlibBridge` (`OuterplanarExportCert`, local `IsOuterplanar` ≃ `IsFacialOuterplanar`, `MathlibIsOuterplanarGap`/`UpstreamHook`, peel hooks, 7 smoke export certs). See `MATHLIB_IS_OUTERPLANAR_MIGRATION.md`.
