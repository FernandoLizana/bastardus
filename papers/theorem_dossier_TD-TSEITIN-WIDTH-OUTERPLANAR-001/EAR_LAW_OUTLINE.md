# Ear law — esquema de prueba (outerplanar Δ≤3)

## Enunciado combinatorio (`earLaw`)

Tras **pelar árboles colgantes** (hojas de grado 1), todo grafo 2-conexo outerplanar con `Δ ≤ 3`
que **no** es un ciclo puro admite al menos uno de:

1. **Oreja triangular**: vértice de grado 2 cuyos dos vecinos son adyacentes (triángulo).
2. **Tip shortcut**: vértice de grado 2 adyacente a un vértice de grado ≥ 3.

En Lean (`Outerplanar.lean`) esto aparece como hipótesis `earLaw` sobre `ResidualSketch`.

## Evidencia E2

| Script | Resultado |
|--------|-----------|
| `outerplanar_ear_existence_mass.py` | **200/200** (muestra original) |
| `outerplanar_ear_existence_mass_n12.json` | Ampliación n≤12 (ver reporte) |

Algoritmo: `peel_trees` → si no es ciclo → `has_triangle_ear ∨ has_shortcut_tip`.

## Esquema de terminación (enlace TERMINATION.md)

```
G outerplanar, Δ≤3
    → peel trees → core 2-conexo G'
    → si G' es ciclo: caso base (Width=Δ o lema ciclo+cuerdas)
    → si no: earLaw da tip v
         → fold en v (path_fold / ear elim)
         → grafo menor, sigue outerplanar, Δ≤3
         → medida ↓ (|V|+|E| o #vértices deg≥3)
```

## Conexión con θ-residuo

`ThetaChordFold.chordFoldLaw` cubre el caso **ciclo + cuerdas** en el residuo después de plegados:
triángulo vs shortcut según internos del arco corto. `earLaw` generaliza la existencia de tip
en **cualquier** core outerplanar no-ciclo.

## Gaps formales

| ID | Gap | Estado 2026-07-18 |
|----|-----|-------------------|
| E1 | `fold_deg2_tip` preserva outerplanaridad | **OK facial** (`OuterplanarEmbedCert.foldTriangle`); **Δ≤3 OK** Mathlib; sin `IsOuterplanar` genérico |
| E1b | Carga impar tras fold | **OK** (`OddChargeFold.gf2Sum_foldTip`) |
| E2 | Medida estrictamente decrece | **OK total** (`foldNormal`, `foldSteps_le`; `GraphFoldPreservation.card_drops`) |
| E3 | Puente `earLaw` → `EliminationStep` | **Upper OK** **∀** `CycleChord.toCycleBase`; lower packs |
| E4 | Inducción global Lean | **OK** oneChord; nested/disjoint/triple peel→ciclo; genérico abierto |
| E5 | Discharge Whitney ear existence | **OK certificado:** `expose` / `CycleChord` / `OuterplanarEmbedCert`; falta solo API Mathlib genérica |

Lean modules: `WhitneyEarAxiom.lean`, `ChordDiagramEar.lean`, `CycleChordEar.lean`,
`OuterplanarBlockCut.lean`, `OuterplanarFoldTermination.lean`,
`OuterplanarOneChordDispatch.lean`, `NestedChordPeel.lean`, `DisjointChordPeel.lean`,
`NestedTripleToCycle.lean`, `NestedChordResidual.lean`, `DisjointChordResidual.lean`.

**One-chord:** `CycleChord.toCycleBase` / `reaches_cycle` covers **every** `CycleChord`
(triangle / fwd / bwd₀ / bwd∀a). Specialized `FacialOneChordPath` schedules remain as
witnesses; `schedule_isSome` proves no `none`.

**Multi-cuerda:** nested/disjoint `peel*ToLen2` → 2-paso inducción (C₁₀→ciclo);
nested-triple: residual → peel → 2-paso (C₁₂→ciclo).

`OuterplanarBlockCut` no sustituye esa API con un booleano: certifica un árbol
enraizado de bloques mediante padres de índice estrictamente menor, índices
válidos de articulación y ears locales para bloques 2-conexos no cíclicos.
El bloque de índice máximo es hoja (`lastIndex_isLeaf`). Si es un ciclo
colgante, la articulación expone `pendantCycleEar`; si no es ciclo, usa el ear
local. Por ello todo certificado distinto de un único ciclo tiene ear legal
(`legalEar_of_not_cycleBase`) y un fold superior (`upper_step`).

Además, `SubcubicOuterplanarBlockCut.nBlocks_eq_one` formaliza la simplificación
específica de este teorema: en un 2-core simple, cada uno de los dos bloques
incidentes a una articulación aporta al menos grado 2; por tanto la articulación
tendría grado ≥4, incompatible con Δ≤3. Así, el caso subcúbico se reduce a un
único bloque 2-conexo (`rootLegalEar`). El extractor gráfico pendiente ya no
necesita desarrollar una inducción completa sobre múltiples bloques.

## Prueba propuesta (pasos)

1. **Lema peel**: pelar hojas no cambia el problema Tseitin esencial (variables de árbol eliminables).
2. **Lema oreja**: si `has_triangle_ear(v)`, eliminar `v` fusionando aristas paralelas mantiene Δ≤3.
3. **Lema shortcut**: si `has_shortcut_tip(v)`, el plegado tip-by-tip es el mismo que en path_fold.
4. **Descenso**: cada fold reduce `|V|`; instancias finitas → terminación.
5. **Empalme** con masa `outerplanar_full_closure_mass.json` (57/57 □ ∈ Closure₃).

## Referencias

- `TERMINATION.md` (mismo dossier)
- `lean/PNPLab/Outerplanar.lean`
- `lean/PNPLab/WhitneyEarAxiom.lean`
- `lean/PNPLab/ThetaChordFold.lean`
