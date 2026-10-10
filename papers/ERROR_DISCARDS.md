# Catálogo ERROR_DISCARDS

**Category:** preparación intelectual claim-gate (Camino A/B) — **no** es una prueba de P vs NP.

Fuente canónica: `backend/claim_gate/catalog.py` (`ERROR_DISCARDS`).
En el gate, **PASS = el modo de error está descartado / no se usa**.

Última sincronización: 2026-07-18.

---

## Para qué sirve

Antes de presentar una resolución de P vs NP, el dossier debe marcar **todos** estos
ítems como descartados. Si alguno queda en uso (FAIL), el claim-gate bloquea.

El trabajo **Width vs Δ** (Category C) **no** intenta Camino A/B; esta ficha documenta
por qué esos modos de error **no** son la narrativa del lab, y qué exigiría un
Camino A hipotético.

---

## Checklist (20 ítems)

| ID | Pregunta (¿usa…?) | Width / Cat. C | Camino A (si hubiera) | Camino B (si hubiera) |
|----|-------------------|----------------|------------------------|------------------------|
| `brute_2n` | ¿Fuerza bruta 2ⁿ? | N/A — no hay algoritmo SAT | Debe descartarse | N/A a LB de resolución |
| `input_dependent_exponent` | ¿Exponente que depende de \|entrada\|? | N/A | Debe descartarse | N/A |
| `exp_precompute` | ¿Tabla precalculada exponencial? | N/A | Debe descartarse | N/A |
| `exp_memory` | ¿Memoria exponencial? | Masa E2 es finita/experimental, no claim asintótico | Debe descartarse | N/A |
| `exp_parallel_branches` | ¿Ramas exp. en paralelo? | N/A | Debe descartarse | N/A |
| `exp_processors` | ¿# procesadores exponencial? | N/A (GPU es heurística de verificación) | Debe descartarse | N/A |
| `exp_bit_integers` | ¿Enteros con bits exponenciales? | N/A | Debe descartarse | N/A |
| `unary_vs_binary` | ¿Complejidad en valor, no longitud binaria? | N/A | Debe descartarse | N/A |
| `pseudo_poly` | ¿Pseudo-polinómico? | N/A | Debe descartarse | N/A |
| `bounded_treewidth_only` | ¿Solo treewidth pequeño? | **Riesgo narrativo:** Δ≤3 / familias planar son restringidas — el lab lo declara Category C, no P≠NP | Camino A no puede limitarse a tw acotado | Camino B: `restricted_model` |
| `clause_ratio_only` | ¿Solo ratio de cláusulas? | N/A | Debe descartarse | N/A |
| `almost_always` | ¿Solo «casi siempre»? | Masses son exhaustivas en rango n, no probabilísticas | Debe descartarse | Debe descartarse |
| `distribution_dependent` | ¿Depende de distribución? | No | Debe descartarse | Debe descartarse |
| `error_prob_unremoved` | ¿Error sin eliminar? | No (determinista) | Debe descartarse | Debe descartarse |
| `neural_no_proof` | ¿Red neuronal sin prueba? | No | Debe descartarse | Debe descartarse |
| `ai_strategy_exp` | ¿IA elige estrategia exp.? | Agentes ayudan a formalizar; no son el claim | Debe descartarse | Debe descartarse |
| `non_terminating` | ¿Puede no terminar? | Algoritmos de masa/certs terminan | Debe descartarse | N/A |
| `small_n_only` | ¿Solo n pequeños? | **Sí en masa** (n≤13 all-odd); por eso **no** se presenta como asintótica Clay | Camino A: FAIL si solo n chico | Camino B: FAIL sin ∀n |
| `curve_fitting` | ¿Ajuste de curvas ⇒ poly? | No se usa | Debe descartarse | Debe descartarse |
| `practice_vs_asymptotic` | ¿Rapidez práctica ≠ poly? | No se confunde | Debe descartarse | Debe descartarse |

---

## Relación con el claim-gate

Evaluación: `backend/claim_gate/evaluate.py` — sección `error_discards`.
Todos los IDs deben PASS (descartados).

Demo Camino B bloqueado (Width ≠ P≠NP):

`reports/discovery/claim_gate_camino_b_resolution_blocked.json`

Allí los error-discards se marcan como N/A a la narrativa de LB de resolución /
sesgos de algoritmo — el **bloqueo** real viene de `restricted_model` y
`b_not_method_specific`, no de estos ítems.

---

## Lectura honesta para el lab

| Señal | Interpretación |
|-------|----------------|
| Mass n≤13 + Lean packs | Category C; ítem `small_n_only` **aplica** si alguien pretendiera Clay |
| Δ≤3 / outerplanar | Ítem `bounded_treewidth_only` **aplica** como advertencia narrativa |
| Claim-gate `may_present=False` | Correcto; no se usa ningún ERROR_DISCARD como “truco” hacia P≠NP |

**Regla:** completar esta checklist en un dossier Camino A/B **antes** de celebrar.
Para Category C, bastan las fichas de barreras + esta tabla como inmunización intelectual.

---

## Referencias

- `backend/claim_gate/catalog.py` — fuente
- `docs/P_VS_NP_CLAIM_GATE.md`
- `papers/BARRIER_RELATIVIZATION.md`, `BARRIER_NATURAL_PROOFS.md`, `BARRIER_ALGEBRIZATION.md`
- `papers/WHY_WIDTH_IS_NOT_P_NE_NP.md`
- `papers/ROADMAP_P_VS_NP.md` (Fase 2.5)
