# XOR residual-split — estado del gap (`gap_remains`)

## Resumen

El intento de **relleno XOR puramente local/gaussiano** tras tip-sum en orejas
length-2 con ambos stubs **falla de forma sistemática**. No es un quirk de C₆.

| Artefacto | Resultado |
|-----------|-----------|
| `xor_gaussian_residual_split.json` | C₆ witness: `gap_remains=true` |
| `xor_gaussian_gap_mass.json` | masa n=5..10 (script) |
| `xor_ear_modes.json` | **39/39** hybrid XOR-sum + residual target-sat OK |
| `XOR_EAR.md` | dossier |

## Qué significa `gap_remains`

Tras `eq_u ⊕ eq_v` en el tip, rellenar `residual_u` / `residual_w` usando
**solo** variables del soporte residual local falla: hace falta cancelación
con variables “puente” (o sat global / clips híbridos).

## Implicación para E5

- Upper bounds outerplanar/bicyclic **no dependen** de cerrar este gap: usan
  path-fold + sat de ancho Δ.
- Un lema XOR algebraico puro sería un **bonus** Category C, no el camino crítico
  hacia crossing law / Width=Δ.

## Criterio de cierre (opcional)

- [x] Enunciado formal de obstrucción: `XOR_OBSTRUCTION_FORMAL.md`
- [x] Stub Lean: `XorObstruction.lean` (C₆ witness + mass constants + GF(2) Nat bookkeeping)
- [ ] Demostrar obstrucción en Lean (álgebra lineal GF(2) completa sobre soportes)
- [ ] O encontrar familia donde local-Gaussian sí basta
- [x] No bloquear proyección / earLaw Lean por este gap
