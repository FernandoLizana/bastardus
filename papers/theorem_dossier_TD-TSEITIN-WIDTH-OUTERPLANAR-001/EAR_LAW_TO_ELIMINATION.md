# earLaw combinatorio → `EliminationStep` (puente E3)

## Objetivo

Conectar la existencia combinatoria de tips (`earLaw`, 298/298 n≤12) con un paso
`EliminationStep` que preserve membresía en `Closure₃` sobre el conjunto residual de variables.

## Estado actual

| Capa | Artefacto | Estado |
|------|-----------|--------|
| Combinatoria | `outerplanar_ear_existence_mass_n12.json` | **298/298** |
| Clasificación | `Outerplanar.lean` `ResidualSketch.classify` | OK |
| Existencia | `earLaw` en sketch | Axioma |
| Plegado Python | `fold_deg2_tip` | OK (masa multihop) |
| Lean eliminación | `EliminationStep` + packs | Instancias concretas |
| Puente upper | `CycleChord.toCycleBase` | **OK**: **∀** one-chord → ciclo (`schedule_isSome`) |
| Nested len-2 (outer ≠△) | `NestedChordToCycle` | **OK**: residual → `toCycleBase` (C₁₂ long) |
| Disjoint len-2 (2nd ≠△) | `DisjointChordToCycle` | **OK**: residual → `toCycleBase` (C₁₂ long) |
| Nested/disjoint long-ear | `NestedLongEarToCycle`, `DisjointLongEarToCycle` | **OK**: peel→Len2→ciclo (C₁₄) |
| Nested-triple long | `NestedTripleLongToCycle` | **OK**: residual→peel→Len2 (C₁₅ outer ≠△) |
| Disjoint-triple | `DisjointTripleToCycle`, `DisjointTripleLongToCycle` | **OK**: C₁₂ Len2 + C₁₅ long |
| Two-chord total | `OuterplanarTwoChordTotal` | **OK**: schedule + `FacialTwoChordPath` |
| Triple-chord total | `OuterplanarTripleChordTotal` | **OK**: schedule + `FacialTriplePath` |
| Nested long-ear | `NestedChordPeel` | **OK**: peel→len2 → 2-paso (C₁₀→ciclo) |
| Disjoint long-ear | `DisjointChordPeel` | **OK**: peel→len2 → 2-paso (C₁₀→ciclo) |
| Nested-triple | `NestedTripleToCycle` | **OK**: residual→peel→2-paso (C₁₂→ciclo) |
| Multi-chord honesty | nested/disjoint triangle+shortcut + triple | **OK**: residuals ≠ ciclo |
| Puente lower | sketch → `EliminationStep` | **OK hop families 1–6**: `foldTipFirstHop` + pack count 7 |

## Esquema del puente (3 pasos)

### Paso 1 — Tip combinatorio → vértice de plegado

Dado `g : ResidualSketch` con `earLaw`:

- Si `hasTriangleEar`: elegir `v` con vecinos adyacentes (Python: `has_triangle_ear`).
- Si `hasShortcutTip`: elegir `v` de grado 2 adyacente a grado ≥ 3.

Lean: `ResidualSketch.classify` ya devuelve `EarTipKind`.

### Paso 2 — Plegado → inclusión de proyección

Para la instancia Tseitin asociada al sketch residual `G`:

1. Aplicar `fold_deg2_tip` en `v`.
2. Verificar (E2) que toda cláusula de `Closure₃(G)` soportada en `V_after` permanece en
   `Closure₃(G')`.
3. Empaquetar como `EliminationStep` con `before` / `after` / `V_after`.

Esto es exactamente lo certificado en los packs `OneFold` … `SixFold` y en la masa
461/461 multihop.

### Paso 3 — Iteración → terminación

Medida: `FoldMeasure.nVertices` (`Outerplanar.lean`).

- `fold_step_decreases`: cada fold no-ciclo reduce vértices.
- Tras `n` folds: ciclo puro o residual empaquetado (16 cláusulas XOR).

## API Lean propuesta (siguiente PR)

```lean
-- Outerplanar.lean (futuro)
structure FoldTipWitness (w : Nat) where
  sketch : ResidualSketch
  tipKind : EarTipKind
  step : EliminationStep w
  matches_sketch :
    sketch.classify.tipKind = some tipKind

theorem earLaw_yields_fold_step (g : ResidualSketch) (h : g.earLaw) :
    ∃ w (W : FoldTipWitness w), True := by
  sorry  -- discharge from classify + E2 mass
```

Hasta entonces, los packs concretos instancian `FoldTipWitness` por `native_decide`.

## Dependencias

- `EAR_LAW_OUTLINE.md` — existencia combinatoria
- `TERMINATION.md` — bucle de terminación
- `ResolutionClosure.lean` — `StepLink`, `LinkedChain`, `projectionOfLinkedTwo`
- `ThetaChordFold.lean` — caso θ-residuo (ciclo + cuerdas)

## Criterio de cierre E3

- [x] Upper-bound: `FacialTriangleFoldStep` empaqueta tip/`FoldTipWitness` + embed + odd charge + measure
- [x] `FoldTipElimination` para crossing lower-bound (`c5CrossingFoldElim` ↔ OneFold)
- [x] `FoldTipWitness` para sketches faciales generados por `CycleChord` triángulo
- [ ] Un fold outerplanar arbitrario de la masa n≤12 se refleja en Lean sin `sorry` (opcional; packs cubren hops)
