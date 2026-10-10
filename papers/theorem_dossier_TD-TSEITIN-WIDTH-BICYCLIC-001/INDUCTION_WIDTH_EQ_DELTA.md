# Inducción Width=Δ para bicyclic Δ≤3 (plan Lean)

## Enunciado objetivo (Category C)

∀ G conectado, γ(G)=2, Δ(G)≤3, carga impar c:
`Width(T(G,c)) = Δ(G)`.

## Descomposición ya disponible

| Paso | Artefacto | Estado |
|------|-----------|--------|
| Peel árboles | Python + Rust constructive | OK |
| 2-core = θ (Cₙ+cuerda) | combinatoria clásica | OK |
| Tip en todo θ-residuo | `ThetaResidue.chordFoldLaw` | **Lean OK** |
| Fold measure ↓ | `Bicyclic.fold_step_decreases` | Lean OK |
| Residual ciclo → Width=2 | cycle lemma / packs | Python + parcial Lean |
| Upper □ ∈ Closure₃ | packs C₄/C₅/C₆ + masa 48/48 | E2 + Lean instancias |

## Esquema inductivo

```
G bicyclic Δ≤3
  → peel → θ = C_n + chord
  → while not cycle:
        tip := chordFoldLaw(θ)     -- Lean: ThetaResidue
        fold tip → θ' smaller
  → cycle odd charge → Width = 2 ≤ Δ
```

Medida: `|V|` (o `shortInternals` + `|V|`).

## Gaps para E5 completo

1. **Peel en Lean** — sketch `OuterplanarPeel` / bicyclic parallel OK a nivel medida; XOR tip peel graph-level abierto.
2. **Fold preserva** membresía Closure_Δ — pathfold E2; **no** ProjectionInclusion en upper packs.
3. **Identificación** residual tras folds = ciclo empaquetado — packs C₄–C₆.
4. **Paramétrico** ∀n,a — `chordFoldLaw` sí; Closure₃ packs.

## Lean G8 scaffold

`BicyclicUpperSketch.lean`: `upperChordFoldStep_exists`, `bicyclic_measure_induction`,
`thetaResidue_feeds_upper`, C₆ triangle bridge.

## No bloqueantes

- XOR gaussiano puro (`gap_remains`) — path-fold + sat bastan.
- Packs n=12 — masa E2; Lean limitado por tamaño Closure.

## Referencias

- `PROOF_PATHFOLD.md`
- `ThetaChordFold.lean`
- `BicyclicWidth3` / `BicyclicC5Width3` / `BicyclicC6Width3`
- `SCALE_LEAN_VS_MASS.md`
