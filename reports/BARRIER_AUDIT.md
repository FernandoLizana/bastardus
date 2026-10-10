# Barrier audit (initial, honest)

Auditoría de flechas **ausentes** hacia P≠NP. Sin reclamos de progreso hacia la separación.

## Flechas que NO existen aún

| De | A | Estado |
|----|---|--------|
| tw(L(G)) = 3/4 (caso k=2 finito) | Cota inferior superpolinomial | **Gap abierto** — ancho constante ≠ asintótico |
| Hipótesis literatura width = max(Δ, tw(L)) | Teorema PNPLab | **Hipótesis condicional** |
| tw(L(G)) = 4 crossing (Python) | `HasTreeDecomp` Lean | **Gap** — solo `ExperimentalTreewidthBound` |
| Familia D_n candidata | tw(L(D_n)) = Ω(n) formal | **Conjetura / dato** |
| Tseitin ancho 3/4 | Hardness SAT | **Gap** — no reducción |
| ChordWidth | P ≠ NP | **Sin implicación** |

## Flechas parciales existentes

| De | A | Tipo |
|----|---|------|
| Literatura + char + φ | ResolutionWidth max(3,k) | Condicional |
| Crossing + K₄ core smoke | Nucleo estructural theta | Teorema finito (smoke) |
| Noncrossing + C₄ core smoke | Nucleo four-branch | Teorema finito (smoke) |
| `TreeDecomp` + trivial | HasTreeDecomp K₄ ≤ 3 | Teorema formalizado |

## Barreras clásicas (no atacadas)

- **Relativización:** no hay oráculo-aware separation.
- **Natural proofs / algebraización:** sin framework.
- **Proof complexity:** width finito en Δ=3 no implica lower bounds SAT generales.

## Recomendación

Priorizar certificado Lean `HasTreeDecomp` para tw(L(G)) en instancias smoke antes de cualquier narrativa de “evidencia” hacia P≠NP.
