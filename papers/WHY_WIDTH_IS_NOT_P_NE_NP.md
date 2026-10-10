# Por qué Width ≠ P vs NP (en este lab)

## Tesis en una frase

Demostrar que **Tseitin restringido** necesita **ancho de resolución > Δ** no es, por sí solo,
una prueba de **P ≠ NP** — y el propio repositorio está configurado para **no** presentar esa
implicación.

## Tres desconexiones estructurales

### 1. Modelo restringido

- **Width** acota el ancho de cláusulas en **resolución** (o variantes similares).
- **P vs NP** pregunta por **algoritmos deterministas polinomiales** para SAT general.
- Un lower bound en un sistema de prueba no implica inexistencia de algoritmos distintos
  (DP, semidefinidos, circuitos, etc.).

### 2. Familias vs problema universal

El lab estudia grafos **outerplanar / bicyclic / ciclo+dos cuerdas** con Δ≤3.

SAT general incluye instancias **sin** esa estructura. Una ley Width=Δ en una subfamilia no
restringe SAT_NP completo.

### 3. Claim-gate Camino B

`demo_camino_b_blocked` reporta `may_present=False`:

- `restricted_model` — el resultado es sobre Tseitin estructurado, no SAT arbitrario.
- `b_not_method_specific` — width no es el método B (circuit lower bounds estándar).

Ver `docs/P_VS_NP_CLAIM_GATE.md` y `reports/discovery/claim_gate_camino_b_resolution_blocked.json`.

## Qué SÍ aporta el programa Width vs Δ

| Aporte | Valor científico |
|--------|------------------|
| Ley cruce ⇔ Width>Δ | Fenomenología precisa en Tseitin planar |
| Packs Lean + masa | Evidencia reproducible, formalización parcial |
| Proyección multihop | Mecanismo constructivo de upper bounds |
| earLaw / chordFoldLaw | Terminación combinatoria candidata |

Esto es **proof complexity estructurada** (Category C/D), no Clay Millennium.

## Barreras relacionadas

- `BARRIER_RELATIVIZATION.md`
- `BARRIER_NATURAL_PROOFS.md`
- `BARRIER_ALGEBRIZATION.md`

## Roadmap honesto

Ver `ROADMAP_P_VS_NP.md`: fases 0–5 separan explícitamente:

- **Fase 0** — claim-gate (hecho: bloqueado)
- **Fases 1–3** — Category C (este lab)
- **Fases 4–5** — puentes hipotéticos hacia SAT general (no iniciados)

## Proximidad estimada a P≠NP vía esta línea

**≈ 0** sin nuevo puente formal no contenido en el repo.
