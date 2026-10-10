# Mapa de tareas: acercarse a P vs NP (paso a paso)

**Regla del laboratorio:** nada por debajo de E5 + claim-gate puede presentarse
como resolución de P vs NP. Este mapa **no** promete llegar; organiza lo que
faltaría y qué se puede hacer *ahora* sin autoengañarse.

Última actualización: 2026-07-15.

---

## Vista rápida (distancia)

```text
[HOY]  Width vs Δ (Category C)  ──evidencia E2/E4──►  teorema local E5
              │
              │  (NO hay puente automático)
              ▼
[MURO] Barreras + “resolución ≠ todos los algoritmos”
              │
              ▼
[LEJOS] Dossier Camino A o B que pase claim-gate
              │
              ▼
[CLAY] Revisión externa (E6+) — fuera de alcance del lab solo
```

Proximidad actual vía Width→P≠NP: **≈ 0** (ya documentado en `FRONTIER_WIDTH_VS_DELTA.md`).

---

## Dos caminos (elige exactamente uno)

| Camino | Afirmación | Qué necesitas en el fondo |
|--------|------------|---------------------------|
| **A** | P = NP | Un algoritmo rápido y correcto para un problema NP-completo |
| **B** | P ≠ NP | Prueba de que **ningún** algoritmo rápido existe (todos, incluso futuros) |

Hoy el lab está mejor posicionado para estudiar **B vía cotas inferiores**, pero
**solo en sistemas de prueba restringidos** (resolución). Eso **falla** el
claim-gate (`restricted_model`). Ver Paso 0.

---

## Fases

### Fase 0 — Diagnóstico (empezar aquí) ✅ en curso

| # | Tarea | Estado | Entrega |
|---|--------|--------|---------|
| 0.1 | Releer claim-gate (`docs/P_VS_NP_CLAIM_GATE.md`) | Hecho | — |
| 0.2 | Ejecutar demo Camino B bloqueado (Width ≠ P≠NP) | **Hecho** | `claim_gate_camino_b_resolution_blocked.json` |
| 0.3 | Escribir “por qué estamos bloqueados” en 10 líneas | **Hecho** | este doc §Paso 0 |

### Fase 1 — Conjeturas intermedias (Category C) — *sí avanzables*

Estas **no** son P vs NP, pero entrenan el músculo de prueba formal y cierran
el hueco de literatura “Width vs Δ”.

| # | Tarea | Estado | Por qué importa |
|---|--------|--------|-----------------|
| 1.1 | Formalizar conjetura Crossing ⇒ Width ≥ 4 | **Norte fijado** | `C-CYCLE-TWO-CHORDS-CROSSING-LAW` |
| 1.2 | Teorema proyección multihop ∀ crossings | **Parcial** | 461/461 E2 + `composeProjection_trans`; fold lista Lean abierto |
| 1.3 | Outerplanar earLaw general (Lean/graph) | **Parcial** | 298/298 n≤12 + `EAR_LAW_OUTLINE.md`; axioma Lean abierto |
| 1.4 | Bicíclico Width=Δ inductivo | Parcial | θ-law ya en Lean |
| 1.5 | Empujar packs → lema paramétrico Lean | Abierta | De E2 a E5 |

**Regla:** cada ítem 1.x debe etiquetarse `Category C/D — not P vs NP`.

### Fase 2 — Entender el muro (lectura + artefactos)

| # | Tarea | Estado | Entrega |
|---|--------|--------|---------|
| 2.1 | Ficha: relativización (qué exige el gate) | **Hecho** | `papers/BARRIER_RELATIVIZATION.md` |
| 2.2 | Ficha: natural proofs | **Hecho** | `papers/BARRIER_NATURAL_PROOFS.md` |
| 2.3 | Ficha: algebrización | **Hecho** | `papers/BARRIER_ALGEBRIZATION.md` |
| 2.4 | Ficha: por qué “Width grande ⇒ P≠NP” es inválido | **Hecho** | `papers/WHY_WIDTH_IS_NOT_P_NE_NP.md` |
| 2.5 | Catálogo de errores descartados (`ERROR_DISCARDS`) | **Hecho** | `papers/ERROR_DISCARDS.md` |

Sin Fase 2, cualquier “casi lo tengo” es ilusión.

### Fase 3 — Puente (solo si aparece una idea nueva)

| # | Tarea | Estado | Nota |
|---|--------|--------|------|
| 3.1 | ¿Existe reducción de “algoritmo general” a “derivación en resolución”? | Open / unlikely | Casi nunca |
| 3.2 | ¿Cota en otro sistema más fuerte (Frege, circuitos)? | Open | Otro proyecto |
| 3.3 | Si hay candidato a puente: someter a claim-gate **antes** de celebrar | Obligatorio | API `/claims/p-vs-np/gate` |

**Hasta que 3.x no tenga un plan concreto, no hay Camino B.**

### Fase 4 — Camino B (solo con puente)

| # | Requisito del gate | Hoy |
|---|-------------------|-----|
| 4.1 | Problema en NP sin algoritmo det. poly | FAIL |
| 4.2 | Cubre algoritmos futuros | FAIL |
| 4.3 | Cota asintótica para n arbitrario | FAIL |
| 4.4 | No limitado a un método (DPLL/resolución/…) | FAIL |
| 4.5 | Modos decision/search/opt + YES/NO | FAIL |
| 4.6 | Barreras abordadas | FAIL (`restricted_model`) |
| 4.7 | E5 Lean + E6 revisión | No iniciado |

### Fase 5 — Camino A (alternativa; hoy no hay pista)

| # | Requisito | Hoy |
|---|-----------|-----|
| 5.1 | Algoritmo NPC | No existe candidato |
| 5.2 | Correcto en todas las entradas | — |
| 5.3 | Tiempo O(n^k) bits | — |
| 5.4 | Sin trabajo exp oculto | — |

El trabajo Width **no alimenta** Camino A.

---

## Orden de avance recomendado (paso a pasito)

1. **Paso 0** — Confirmar bloqueo Camino B con Width (esta sesión).
2. **Paso 1** — Elegir **una** conjetura Category C como “norte” (Crossing Width≥4).
3. **Paso 2** — Trabajar 1.2 proyección paramétrica *o* 1.3 earLaw (elige uno).
4. **Paso 3** — Fase 2 fichas de barreras (1 ficha por sesión).
5. **Solo después** reevaluar si hay idea de puente (Fase 3).

---

## Paso 0 — Por qué Width no pasa Camino B (borrador)

Afirmar P≠NP usando solo “resolución necesita ancho grande en algunos Tseitin”
falla porque:

1. Solo limita **un** método de prueba (resolución), no todos los algoritmos.
2. El gate exige `b_not_method_specific` y marca `restricted_model`.
3. Cotas en n≤10 / instancias concretas no dan asintótica para n arbitrario.
4. No cubre algoritmos futuros ni circuitos generales.

Evidencia del lab: `reports/discovery/claim_gate_camino_b_resolution_blocked.json`.

---

## Cómo medir progreso sin mentirnos

| Señal | Significa avance real hacia P vs NP? |
|-------|--------------------------------------|
| Más packs Lean / masa E2 | No (Category C) |
| Teorema Width vs Δ E5 | No (sí cierra literatura local) |
| Nota que explica barreras | Sí (preparación intelectual) |
| Idea de puente + pasa claim-gate parcial | Sí (primer contacto real) |
| Claim-gate `may_present_as_resolution=true` | Único “casi” del lab |

---

## Próxima acción concreta

**Hecho ahora:** mapa + Paso 0 (claim-gate: `may_present=False`).

**Norte Category C (Paso 1):** conjetura
`C-CYCLE-TWO-CHORDS-CROSSING-LAW` — crossing ⇔ Width>Δ; noncrossing ⇔ Width=Δ
(Δ≤3, carga impar). Evidencia fuerte; falta E5 de familia (proyección ∀ +
earLaw outerplanar).

**Siguiente “proceda”:** trabajar **1.2** (proyección multihop paramétrica) *o*
**1.3** (earLaw outerplanar), un solo frente por vez.
