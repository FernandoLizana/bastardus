# E5 — Proyección multihop a nivel familia (Category C)

## Objetivo

Demostrar inductivamente que **toda** instancia Tseitin en ciclo + dos cuerdas cruzadas admite una
cadena de proyecciones por plegado tip-by-tip que preserva `Closure_w` en el conjunto residual de
variables, hasta un residual de ancho acotado (típicamente 16 cláusulas XOR en 4 variables).

Esto es el paso **E5** hacia la ley de cruce `C-CYCLE-TWO-CHORDS-CROSSING-LAW` (Width > Δ ⇔ cuerdas cruzan).

## Evidencia empírica (E2 → E4)

| Artefacto | Resultado |
|-----------|-----------|
| `multihop_projection_mass.json` | **461/461** instancias n=5..10 |
| `multihop_chains_full.json` | Cadenas compactas (hop_sizes, tips≤6) |
| `multihop_chains_export.json` | Muestra con conjuntos `vars` por hop |
| Packs Lean `OneFold` … `FiveFold` | Cadenas 1–5 saltos entre **closures empaquetados** |
| `ThetaChordFold.chordFoldLaw` | Tip combinatorio en residuo θ (triángulo vs shortcut) |

## Infraestructura Lean (composición)

En `ResolutionClosure.lean`:

- `composeProjection` / `composeProjection3` … `composeProjection6` — composición fija de N hops
- `composeProjection_trans` — **transitividad** de dos proyecciones con puente `P₁.rClosure = P₂.gClosure`
- `varsSubset_trans` — anidamiento monótono `V₂ ⊆ V₁` a lo largo de la cadena
- **`eliminationOfLinkedChain` / `projectionOfLinkedChain`** — fold genérico sobre
  `LinkedChain` arbitraria (G2); packs Multi/Triple/Four/Five/Six usan este fold

Los packs actuales prueban cadenas **concretas** con `native_decide` sobre membresía en closures finitos.

## Esquema inductivo E5 (borrador)

### Hipótesis de instancia

- Grafo `G = C_n + {e₁,e₂}` con cuerdas cruzadas en el embedding circular.
- Carga impar Tseitin en vértices de grado 3 (cuerdas) y par en el resto.
- `Δ(G) = 3`, objetivo `w = 3`.

### Paso base (n pequeño)

Instancias n=5,6 ya cubiertas por packs (`BicyclicC5Width3`, `LongArcProjection`, etc.).

### Paso inductivo (idea)

1. **Descomposición por arcos** (`crossing_branch_sets`): dos ramas entre extremos de cuerdas.
2. **Plegado tip-by-tip** en cada rama (`fold_deg2_tip`): cada hop es un `EliminationStep` con
   `V_after` = variables de aristas del grafo residual.
3. **Monotonía** (verificado 461/461): `V_{i+1} ⊆ V_i` en cada hop.
4. **Puente entre ramas**: tras agotar una rama, el grafo residual coincide con el de una instancia
   menor o con el patrón θ-residuo (`chordFoldLaw`).
5. **Composición**: encadenar hops con `composeProjection` / `composeProjection_trans` hasta el
   residual empaquetado conocido (16 cláusulas).

### Lo que falta para teorema ∀n (no solo masa)

| Gap | Descripción | Estado |
|-----|-------------|--------|
| G1 | Lema paramétrico: cruce ⇒ tip legal en cada etapa | **OK** (`CrossingEndpoints` + frontier) |
| G2 | Fold genérico sobre `LinkedChain` | **OK** |
| G3 | Identificación residual ↔ catálogo | Packs + 461 catalog OK; síntesis ∀n abierta |
| G4 | `□ ∉ Closure₃(R)` ⇒ `□ ∉ Closure₃(G)` | OK en packs |
| Hop window | `n≤10` ⇒ `total≤6` | **OK** (`crossing_hop_budget_le_pack_window`) |

## Relación con P vs NP

Category C/D. Claim-gate Camino B bloqueado. Ver `ERROR_DISCARDS.md`, `ROADMAP_P_VS_NP.md`.

## Próximos pasos concretos

1. ~~`projectionOfLinkedChain`~~ — hecho.
2. G6 outerplanar: ear **derivado** en diagramas noncrossing (`ChordDiagramEar`) — hecho; 2-core general abierto.
3. ~~G3 packs topology set-eq~~ — hecho.
4. G5 Closure₃ síntesis más allá del catálogo (alto costo).

## Avance count-level (G5 esqueleto)

`CrossingFoldSchedule.lean`:
- `CrossingArcs.foldSome` — elige el primer arco positivo (frontera izq)
- `foldSome_total` — cada fold baja `total` en 1
- `foldIter_total` — tras `steps` folds, `total' = total - steps`
- `reaches_k4` — **∀** residual cruzado alcanza el esqueleto K₄ en exactamente
  `total` folds shortcut (nivel de conteo)
- Puente `OpenArcPath` → `FoldTipElimination` (`openArcElim`, `c5_openArc_bridge`)

Esto cierra el **esqueleto ∀n del schedule** a nivel de conteo/medida; sigue
faltando la identificación sintáctica del residual con el catálogo (G3) y el
cierre de `Closure₃` paramétrico (G4) — que permanecen en packs concretos.

`K4ResidualCatalog.lean` (G3 combinatorio):

- `total_zero_iff_k4` — único skeleton con `total = 0`
- `reaches_k4_skeleton` — schedule completo = `K4Skeleton`
- `catalogWitness` — hop budget + template `k4Closure` (16 axioms)
- `maxCrossingHopBudget = 6` (mass)

`K4ResidualID.lean` (G3 shape + rename):

- `ResidualK4Shape` — `|V|=6`, `|Cl|=16`
- Packs One/Multi/FourFold cableados; `VarRename` al template `{1..6}`
- E2: `multihop_k4_residual_shape_mass.json` **461/461**

`MembershipTransport.lean`:

- OneFold residual **set-equal** to `k4Closed`
- Packs 2–6: topology-aware edge bijections map residual sets exactly to
  `k4Closed` (`all_packs_topology_set_eq`)
- Search report `signed_k4_pack_isomorphisms.json`: **6/6** witnesses;
  no variable complementation was required

`CrossingPackCatalog.lean` (G5 routing):

- `packFamilyOfHops` — hop budget `h∈[1,10]` → OneFold…TenFold
- `crossing_pack_route` — pack family + topology set-eq + □-free projection
- `crossing_route_from_arcs` — schedule → K₄ skeleton + pack route
- E2 mass `crossing_hop_pack_catalog_mass.json`: **461/461** tips ∈[1,6]
  (hist 5+15+35+70+126+210); Lean window extended to hop 10 (n≤14 = all-odd)
- Does **not** synthesize a fresh Closure₃ for arbitrary instances

`ParametricClosure3.lean` (G5 transfer):

- `renamedSubset_no_empty` — topology subset ⇒ □∉ residual
- `ParametricClosure3Goal` checklist + `parametric_goal_from_arcs`
- WidthClosures beyond packs 1–6: **OK** (alts 6 + samples 96 + catalog 461)
- OneFold…TenFold ProjectionInclusion: **OK** (n=5..14)
- `parametric_goal_of_mass_window` — ∀ endpoints n∈[5,14] → `ParametricClosure3Goal`
- `residualAxioms` / `residualSynthFromEndpoints` — pack-free template K₄ residual
- `projectionInclusion_of_mass_window` — ∀e n∈[5,14] pack-routed G→R □-free
- Iso bridges: `residualAxioms_perm_ofoldR`, `all_packs_iso_to_residualAxioms`, `all_alt_iso_to_residualAxioms`, catalog 461 + samples 96
- Self-projections beyond packs (R→R): alt1..6, rc1, samp1
- Fresh G₀→R seeds + `mass_window_has_fresh_g0`; scaffold `CrossingEndpointsGraph` (`edgeVar`/`toSimpleGraph`)
- Global-edge: `edgeVar` ∀e matches Python; residual XOR + rename post-fold still open
- Local `IsOuterplanar` ≃ facial; typed `MathlibIsOuterplanarGap` + `MathlibIsOuterplanarAbsent` (upstream absent v4.32); **scaffold complete, upstream blocked** — see `MATHLIB_IS_OUTERPLANAR_MIGRATION.md`
- Open: Closure₃(G_e) ∀e; residual XOR under fold; Mathlib export of outerplanarity (blocked on upstream predicate)


`CrossingResidualCatalog.lean` + E2:

- Script `emit_crossing_residual_catalog.py`
- Mass: **461/461** shape + signed iso to `k4Axioms`; **0 flips**
- Tip hist matches hop→pack (5+15+35+70+126+210)
- `topology_subset_residual_shape` transfer principle

`AltResidualWitnesses.lean`:

- 6 non-canonical crossings (one per hop 1..6)
- `all_alt_topology_set_eq` — G3 beyond the six emit packs

`ResidualSampleCatalog.lean`:

- 96 stratified non-canonical crossings (≥16 per hop 3..6, thirteen at hop-2, three at hop-1 — catalog caps; surplus cascades)
- `all_sample_topology_set_eq` — G5 residual WidthClosure sample beyond packs + alts

`CrossingTopologyPermLookup.lean` (E5 open 2 — topology perm dst):

- `endpointsLookupKey` → 10 perm classes (`topologyPermForEndpoints`); **461/461** unique keys
- `topologyPermForArcs` / `topologyPermForArcsOf` — **partial** `(n, toArcs)` lookup: **83/461** instances, **83/209** arc shapes unique; **126/209** ambiguous (**378/461** instances need endpoint placement)
- **`topologyPermForArcsP0` / `topologyPermForArcsP0Of`** — **461/461** via minimal partial key `(n, toArcs, p0)` (no p1..p3); `(n, toArcs, p1)` also 461/461; agrees with full endpoint hash (`topologyPermArcsP0EndpointAgreementFlags_mass`)
- Analysis: `backend/proof_complexity/analyze_topology_perm_arcs.py` → `reports/discovery/topology_perm_arcs_analysis.json`
- Weaker keys insufficient: cyclic arc normalization (**0/461**; all 55 shapes multi-perm); `(n, arcs, Vres)` **459/461** (sole collision: n=6, arcs=(1,0,0,1), Vres=[2,4,5,6,7,8], catalog idx 10 vs 18 — Lean `topologyPermArcsVresCollision_*`, witnesses `c6Endpoints0234`/`c6Endpoints1345`)
- **Sin forma cerrada combinatoria (honesto):** perm dst = iso firmado K₄ de E2; 126/209 formas de arco multi-perm; invariantes de schedule (total, hop, sorted arcs)+p0 colisionan en catálogo; cobertura 461/461 solo vía tabulación emit (`topologyPermForArcsP0Of` / `endpointsLookupKey`). Ver `topologyPermNoClosedFormDoc`, `closed_form_verdict` en JSON.
- Smokes: c5Alt1 arcs-unique (`topologyPermForArcs` = some); c5Ofold/c6 arcs-ambiguous but **arcs+p0-unique**
- Bridge: `parametricEndpointsGoal_of_witnesses_arc_perm` / `_arc_p0` in `ParametricCombinatorialDischarge`


## Referencias

- `papers/theorem_dossier_TD-TSEITIN-WIDTH-CYCLE-TWO-CHORDS-001/PROOF_PROJECTION_E4.md`
- `lean/PNPLab/ThetaChordFold.lean`
- `reports/discovery/multihop_chains_full.json`
