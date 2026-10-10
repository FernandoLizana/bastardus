# E5 gaps — Crossing law / proyección familia (Category C)

Norte: `C-CYCLE-TWO-CHORDS-CROSSING-LAW`  
(crossing ⇔ Width > Δ; noncrossing ⇔ Width = Δ) en Cₙ+2 cuerdas, Δ≤3.

## Checklist de gaps

| ID | Gap | Estado | Artefacto |
|----|-----|--------|-----------|
| G1 | Tip legal en cada hop | **OK** | `CrossingEndpoints.toArcs`; embed; frontier |
| G2 | Fold genérico LinkedChain | **OK** | `projectionOfLinkedChain` |
| G3 | Residual ↔ pack K₄ | **OK packs+alts+samples** | topological set-eq |
| G4 | □∉R ⇒ □∉G | **OK** | packs / `no_empty_of_linkedChain` |
| G5 | ∀n crossings paramétrico | **OK catalog + hop window** | 461/461 closures; `crossing_hop_budget_le_pack_window` (n≤14 ⇒ total≤10) |
| G6 | Outerplanar upper ∀ | **Fuerte** | **∀ CycleChord** + Two/Triple `Facial*Path`; nested/disjoint 2-/3-chord; Δ≤3 |
| G7 | XOR residual-split | **Parcial OK** | 2-/3-span C₆ — no bloquea |
| G8 | Bicyclic Width=Δ | **Fuerte** | pathfold 210/210 + Lean packs |

## Evidencia E2/E4

- Multihop / tips / frontier / K₄ shape: **461/461**
- Outerplanar ear: **701/701**; Closure_Δ∋□ densas
- Bicyclic Closure_Δ∋□: 48/48; pathfold 210/210
- All-odd crossing law: **394768** (n=5..14)

## Distinción importante (proyección)

| Capa | Estado |
|------|--------|
| Schedule combinatorio ∀ (arcs → K₄ en `total` hops) | **Paramétrico** (`reaches_k4_skeleton`) |
| Routing hop≤10 → pack family | **OK** para n≤14 (`crossing_hop_budget_le_pack_window`) |
| Closure₃ sintética por instancia arbitraria | **Catálogo** 461 + 10 packs — no síntesis ∀n |
| Ear-fold hasta base (terminación + cota folds) | **OK total** (`foldNormal_atBase`, `foldSteps_le`) |
| Whitney para bloques/articulaciones certificados | **OK constructivo** (`expose` → `OuterplanarCoreExposure`, sin `Classical.choose`); subcúbico → bloque único |
| Fold preserva Δ≤3 en `SimpleGraph` | **OK** (`maxDegree_le_three_after_delete_tip`, `GraphFoldPreservation`) |
| Ciclo+cuerda → grafo + block-cut | **OK** (`CycleChord.toSimpleGraph`, `toBlockCut`, `expose_ear`) |
| Outerplanaridad tras fold (facial) | **OK** one-chord → ciclo; multi-chord: ear projection ≠ full residual |
| Residual nested 2-chord tras ear triángulo | **OK** (`residualOuterChord` / `afterInnerTriangle` sigue `oneChord`) |
| Residual global + topology rename (parametric smoke) | **OK c5/c6 + n=7..10** (`GlobalRename`, `SmokeMass`, `ParametricProjection`) |
| Parametric discharge catalog (461 Lean) | **OK build** | `ParametricDischargePart1/2/3` + `ParametricDischargeAll`; Prop bridge `ParametricCombinatorialBridge` |
| Combinatorial discharge gap (E5 open 1) | **Parcial** | `ParametricCombinatorialDischarge`: `ForAll↔Witnesses`; fixed-n/range/mass-window subclasses; `parametricDischargeReducesToArcP0`/`ArcUnique` + `ParametricArcP0GoalSufficient`; saturate→`WidthClosure`; perm-agrees rename; `ParametricCombinatorialGoalSufficient`; arc-unique 83/461; arc-p0 461/461; mass-window precond (necessary not sufficient); emit 461/461 contrast; **abierto** combinatorial `parametricDischargeCombinatorialForAll` sin emit (blocker = Bool saturate witnesses) |
| Topology perm lookup (10 classes) | **OK catalog** | `CrossingTopologyPermLookup`, `globalTopologyRenameFor`, `topologyPermForCatalogIndex`; partial `topologyPermForArcs`/`topologyPermForArcsOf` (83/461); **`topologyPermForArcsP0`/`topologyPermForArcsP0Of` (461/461, minimal key `(n,toArcs,p0)`)**; Vres collision 459/461 (`topologyPermArcsVresCollision_*`, `c6Endpoints0234`/`1345`); arcs-only insufficient (126/209 multi-perm); **sin forma cerrada combinatoria sin tabulación** (`topologyPermNoClosedFormDoc`, `closed_form_verdict`) |
| Mathlib export bridge | **OK scaffold, upstream blocked** | `OuterplanarExportCert`, peel→`cycleGraph`; `isOuterplanarEquivIsFacialOuterplanar`; `IsFacialOuterplanar.fromExport`; `MathlibIsOuterplanarAbsent`/`Search`/`Anchors`; peel hooks; `canonical_smoke_export_certs`; `mathlibOuterplanarBridgeBundle`; see `MATHLIB_IS_OUTERPLANAR_MIGRATION.md` |
| Residual disjoint 2-chord tras first ear | **OK** (`residualSecondChord` / `afterFirstTriangle`; C₈ `{3,5}` on 7) |
| Inducción nested/disjoint triángulo→mid→ciclo | **OK** (`NestedTriangleInduction`, `DisjointTriangleInduction`) |
| Nested len-2 → ciclo (outer residual ∀) | **OK** (`NestedLen2Induction` + `CycleChord.toCycleBase`; C₁₂ long) |
| Disjoint len-2 → ciclo (second residual ∀) | **OK** (`DisjointLen2Induction` + `CycleChord.toCycleBase`; C₁₂ long) |
| Nested/disjoint long-ear → Len2 → ciclo | **OK** (`NestedLongEarInduction`, `DisjointLongEarInduction`; C₁₄) |
| Nested-triple long residual → Len2 → ciclo | **OK** (`NestedTripleLongInduction`; C₁₅ outer ≠△) |
| Disjoint-triple → Len2 / long → ciclo | **OK** (`DisjointTripleToCycle`, `DisjointTripleLongToCycle`; C₁₂/C₁₅) |
| Two-chord schedule / facial path | **OK** (`OuterplanarTwoChordTotal`; `schedule_isSome`, `FacialTwoChordPath`) |
| Triple-chord schedule / facial path | **OK** (`OuterplanarTripleChordTotal`; `FacialTriplePath`) |
| FoldTip → EliminationStep (E3 lower) | **OK** (`foldTipFirstHop` ∀ `CrossingPackFamily`; pack count 11) |
| IsFacialOuterplanar (local) | **OK** (`IsFacialOuterplanar`; no Mathlib claim) |
| CrossingEndpoints hop-1..10 → Elim | **OK** (`CrossingEndpointsElim`; C₅..C₁₄) |
| Alt / sample / catalog WidthClosures | **OK** (6 + 96 + **461**) |
| LongEar auto-len2 | **OK** (peel triangle/`nPos`; residual hyps on peeled) |
| Fold facial shortcut (arco corto ≥2) | **OK** (`FacialShortcutFoldStep`; fwd + bwd₀ wrap) |
| Cadena shortcut→triángulo→ciclo | **OK** (`FacialFwdChain3` + `peelToTriangle` ∀k; C₈/C₁₀) |
| Residual nested tras shortcut (ear larga) | **OK** (`NestedChordShortcut`; C₁₀ mid≠ciclo, ear↓) |
| Residual disjoint tras shortcut (ear larga) | **OK** (`DisjointChordShortcut`; C₁₀ mid≠ciclo) |
| Peel bwd wrap ∀k → ciclo | **OK** (`OuterplanarBwdPeel`; C₉ `{0,5}` → C₆) |
| Despacho oneChord unificado | **OK** (`FacialOneChordPath` + **`CycleChord.toCycleBase` ∀**) |
| Bwd ∀a parametric | **OK** (`BwdShortcut.toCycleBaseAny`) |
| One-chord totality | **OK** (`schedule_isSome`, `CycleChord.reaches_cycle`) |
| Nested ear larga → peel len2 → 2-paso ciclo | **OK** (`NestedChordPeel`; C₁₀ → C₈-style → ciclo) |
| Disjoint ear larga → peel len2 → 2-paso ciclo | **OK** (`DisjointChordPeel`; C₁₀ → ciclo) |
| Nested-triple → residual → peel → 2-paso ciclo | **OK** (`NestedTripleToCycle`; C₁₂ → ciclo) |
| Residual nested-triple tras ear interior | **OK** (`NestedTripleResidual`; C₁₂ → nested pair on 11) |
| Carga impar GF(2) tras fold tip | **OK** (`gf2Sum_foldTip`, `OddChargeVec.foldTip`) |
| Paso fold facial unificado (E3 upper) | **OK** (`FacialTriangleFoldStep.bundle`) |
| Inducción facial → ciclo base | **OK** one-/two-/triple-chord `Facial*Path`; nested/disjoint leaf inductions |

## Lo que queda para E5 “completo”

1. ~~461/461 parametric discharge (emit + Lean build)~~ **OK**; ~~perm lookup + export scaffold~~ **OK**; Prop bridge (`closureFromSaturated`, `parametricProjHolds`, discharge⇒FreshG0) **OK**; **parcial** combinatorial gap (`ParametricCombinatorialDischarge`: `ForAll↔Witnesses`, fixed-n/range/mass-window subclasses, `parametricDischargeReducesToArcP0`/`ArcUnique`, `ParametricArcP0GoalSufficient`, perm-agrees rename, `ParametricCombinatorialGoalSufficient`, arc-unique 83/461, arc-p0 461/461, mass-window precond, canonical smoke 7/461); **abierto**: combinatorial `parametricDischargeCombinatorialForAll` — blocker is per-instance saturate Bool witnesses on `closure3`/`residualGlobalAxioms`, not topology perm (461/461 via `(n,toArcs,p0)` tabulation) + Mathlib upstream `IsOuterplanar`.
2. ~~All-odd / hop window / residualAxioms template~~ **OK**.
3. ~~Embedding Mathlib upstream `IsOuterplanar`~~ **scaffold complete, upstream blocked** (PNPLab closed 2026-07-30; `MathlibBridge` + `MATHLIB_IS_OUTERPLANAR_MIGRATION.md`: local `IsOuterplanar` ≃ `IsFacialOuterplanar`, export roundtrips, peel hooks, mass-window + 7 smoke export certs; Mathlib v4.32.0 re-verified — 88 SimpleGraph files, 0 outerplanar/planar API).
## Fuera de este norte

- P vs NP / Camino A|B — ver `ERROR_DISCARDS.md`, barreras
- Packs \|Cl\| ≫ 500

## Referencias

- `FAMILY_PROJECTION_E5.md`, `ERROR_DISCARDS.md`, `QUEUE_AUTONOMOUS.md`
- `lean/PNPLab/OuterplanarOneChordTotal.lean`, `OuterplanarOneChordDispatch.lean`, `OuterplanarBwdPeelPos.lean`, `OuterplanarBwdPeelAny.lean`, `NestedChordPeel.lean`, `DisjointChordPeel.lean`, `NestedTripleToCycle.lean`, `NestedChordResidual.lean`, `DisjointChordResidual.lean`, `OuterplanarShortcutPeel.lean`, `OuterplanarBwdPeel.lean`
- Mathlib: `v4.32.0`
