# Category C / E5 — export para ChatGPT

Generado: 2026-08-02

## Veredicto

- **Infra Category C: cerrada** — 461/461 emit, perm lookup, bridge Prop, Mathlib scaffold
- **Build:** `lake build PNPLab` GREEN — 31 jul 2026 18:41 (1368 jobs)
- **3 techos abiertos** (límites documentados, no bugs):
  1. Combinatorial discharge ∀e sin emit
  2. Perm sin forma cerrada combinatoria
  3. Mathlib `SimpleGraph.IsOuterplanar` (upstream blocked)

## Contenido del archivo

| Carpeta/archivo | Qué es |
|-----------------|--------|
| `papers/REMAINING_CHECKLIST.md` | Checklist maestro |
| `papers/E5_GAPS_CHECKLIST.md` | Gaps G1–G8 + evidencia numérica |
| `papers/MATHLIB_IS_OUTERPLANAR_MIGRATION.md` | Puente Mathlib + verificación upstream |
| `papers/FAMILY_PROJECTION_E5.md` | Proyección familia G→R |
| `papers/WHY_WIDTH_IS_NOT_P_NE_NP.md` | Por qué esto ≠ P vs NP |
| `papers/CROSSING_LAW_ANSWER.md` | Crossing law |
| `papers/FRONTIER_WIDTH_VS_DELTA.md` | Frontera Width vs Δ |
| `canvas/category-c-e5-hallazgos.canvas.tsx` | Síntesis visual (Cursor Canvas) |
| `build/build-resume.state.json` | Prueba último build OK |
| `reports/` | JSON mass / perm analysis (si presente) |

## Fuera de alcance

P vs NP directo — `may_present=False`.
