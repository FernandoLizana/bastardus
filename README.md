# Bastardus — Laboratorio de investigación (P vs NP / ChordWidth) y estudio de IA en matemáticas formales

> **Este repositorio documenta un estudio empírico:** cómo se comportan modelos de IA (agentes de código + asistentes) al atacar un problema matemático duro, con evidencia computacional, formalización en Lean 4 y disciplina de honestidad científica.
>
> **No es una resolución de P vs NP.** Nada por debajo del nivel de evidencia **E5** (verificado en Lean) debe presentarse como tal.

| | |
|---|---|
| **Estado del repo** | **Privado** (preparado para publicación posterior) |
| **Clasificación científica** | **PARTIAL FORMAL PROGRESS** |
| **Conjetura estrella (G1)** | tw(L(G))=3 (noncrossing) / 4 (crossing) para Cₙ + 2 cuerdas válidas — **∀n sigue OPEN** |
| **Evidencia E2 clave** | **2870 / 2870** configs Δ=3, n=5..14, **0 contraejemplos** (treewidth exacto) |

---

## 1. Propósito del estudio (IA × matemáticas)

Este proyecto se usó como **banco de prueba controlado** para observar, medir y documentar el comportamiento de modelos de IA al:

1. **Formular** un problema formal (familia de grafos + conjetura de treewidth del line graph).
2. **Buscar contraejemplos** de forma adversarial (antes de “creer” la conjetura).
3. **Elegir rutas de prueba** y abandonar las inviables con evidencia (matrices de rutas, obstrucciones).
4. **Formalizar en Lean 4** (Mathlib) con reglas duras: sin `sorry` / axioms locales en el track ChordWidth.
5. **Mantener el build verde** y clasificar resultados como PROVED / OPEN / PARKED con honestidad.

### 1.1 Preguntas de investigación (sobre la IA, no solo sobre el teorema)

| Pregunta | Qué observamos en este repo |
|----------|-----------------------------|
| ¿Puede un agente cerrar un ∀n a partir de smokes finitos? | No: muchos certificados finitos ≠ teorema universal. Los agentes tienden a sobre-generalizar desde n=5..14. |
| ¿Ayuda la búsqueda de contraejemplos? | Sí: 2870 configs exactas anclan la conjetura en E2 y frenan rutas falsas. |
| ¿Dónde se atascan los modelos? | Preconnected / RI en plantillas fijas; puentes globales que rompen el build; “arreglos” locales que no escalan. |
| ¿Qué protocolos ayudan? | Matrices de rutas, clasificación PROVED/OPEN/PARKED, prohibición de `sorry`, farm CPU portable con checkpoints. |

### 1.2 Conclusiones metodológicas (basadas en el trabajo registrado)

1. **La evidencia computacional finita es necesaria pero insuficiente.** n=5..14 con 2870/2870 matches **soporta** la dicotomía; **no la prueba** para todo n.
2. **Plantillas fijas se agotan.** Path/fork de 6–7 nodos para c8 a width ≤4 resultaron **inviables** (hub de card ≥6) → pivot correcto a **GenericDecomp paramétrico**.
3. **Cambios globales en adjuntas Lean son peligrosos.** Un bridge en `genericDecompAdj` provocó ~100 errores de compilación; se revirtió. Los certificados extendidos (c8) funcionaron sin mutar la adjunta global.
4. **Los agentes avanzan bien en infraestructura** (indexación de aristas, bags, transporte Fin, Route B `isTree_of_shape`) y **mal al saltar a ∀n** sin diseño de hub paramétrico.
5. **Paralelizar agentes sobre el mismo archivo Lean grande falla**; conviene lanes con archivos/diseños separados.

Detalle vivo de rutas: [`reports/CHORDWIDTH_PROOF_ROUTE_MATRIX.md`](reports/CHORDWIDTH_PROOF_ROUTE_MATRIX.md) · informe AI: [`reports/CHORDWIDTH_AI_FINAL_REPORT.md`](reports/CHORDWIDTH_AI_FINAL_REPORT.md).

---

## 2. Resultados cuantitativos (datos del repo)

### 2.1 Treewidth exacto — línea gráfica de Cₙ + 2 cuerdas

Fuente: [`reports/CHORD_TREewidth_EXACT_N5_N14.md`](reports/CHORD_TREewidth_EXACT_N5_N14.md), CSV [`reports/chord_treewidth_exact_n5_n14.csv`](reports/chord_treewidth_exact_n5_n14.csv).

| Métrica | Valor |
|---------|------:|
| Rango n | 5 .. 14 |
| Configs gap-pattern totales | 3000 |
| Válidas (Δ = 3) | **2870** |
| Degeneradas (excluidas) | 130 |
| Crossing válidas | 1000 → tw = **4** |
| Noncrossing válidas (nested+disjoint) | 1870 → tw = **3** |
| Matches / mismatches | **2870 / 0** |
| Métodos | exact_bruteforce 56 · exact_width_search 2814 |
| Runtime (run documentado) | ~1013 s |

### 2.2 Búsqueda adversarial de contraejemplos

Fuente: [`reports/CHORDWIDTH_COUNTEREXAMPLE_SEARCH.md`](reports/CHORDWIDTH_COUNTEREXAMPLE_SEARCH.md), [`experiments/chordwidth_counterexamples/results.json`](experiments/chordwidth_counterexamples/results.json).

| Métrica | Valor |
|---------|------:|
| Valid configs | 2870 |
| Counterexamples | **0** |
| Status | `NO_COUNTEREXAMPLE_IN_RANGE` |
| Wall time (run documentado) | ~100 s |

### 2.3 Formalización Lean (snapshot)

| Ítem | Estado |
|------|--------|
| Build `lake build PNPLab.ChordWidth.Main` | Verde (~1271–1278 jobs en sesiones documentadas) |
| `sorry` / axioms locales en ChordWidth | 0 (auditoría) |
| Smokes / certificados finitos HasTreeDecomp | PROVED (familia c5–c10 + c8 vía CertificatesLine / C8Extended) |
| Route B (`isTree_of_shape`, edge tags) | PROVED |
| longArc edgeCover | PROVED |
| G1 dicotomía ∀n | **OPEN** |
| G2 núcleo K4/C4 ∀n | **OPEN** |
| G5 Tseitin crossing | **OPEN** / parcial |

### 2.4 Farm CPU portable (pendiente de corridas largas)

Manifest en [`portable_cpu/`](portable_cpu/) — sweeps n=15..32, hub search, Route F+A intervals, perfil high-RAM. Ver [`portable_cpu/TASKS.md`](portable_cpu/TASKS.md).

---

## 3. El programa matemático (ChordWidth / Route F+A)

### 3.1 Objeto

Sea \(G = C_n\) más **dos cuerdas** con cuatro extremos distintos y \(\Delta(G)=3\).

**Conjetura (G1):** en el line graph \(L(G)\),

- cuerdas **no cruzadas** ⇒ \(\mathrm{tw}(L(G)) = 3\)
- cuerdas **cruzadas** ⇒ \(\mathrm{tw}(L(G)) = 4\)

para todo \(n\) admisible.

Enunciado formal: [`reports/CHORDWIDTH_FORMAL_PROBLEM_STATEMENT.md`](reports/CHORDWIDTH_FORMAL_PROBLEM_STATEMENT.md).

### 3.2 Diagrama del pipeline

\\	ext
┌──────────────────┐     ┌─────────────────────┐     ┌──────────────────┐
│  Generación G    │────▶│  L(G) + treewidth   │────▶│  CSV / JSON E2   │
│  C_n + 2 chords  │     │  scripts/treewidth  │     │  reports/        │
└────────┬─────────┘     └─────────────────────┘     └──────────────────┘
         │
         ▼
┌──────────────────┐     ┌─────────────────────┐     ┌──────────────────┐
│  Crossing law    │────▶│  Conjetura G1       │────▶│  Lean ChordWidth │
│  (Python)        │     │  + rutas A–G        │     │  GenericDecomp   │
└──────────────────┘     └─────────────────────┘     └────────┬─────────┘
                                                              │
                                                              ▼
                                                     ┌──────────────────┐
                                                     │  E5 parcial      │
                                                     │  smokes / Route  │
                                                     │  F+A scaffold    │
                                                     └──────────────────┘
\
### 3.3 Diagrama de decisión (rutas)

```text
                    ┌─ Route F (path decomp en arcos) ── SELECTED
                    │
 Rutas A..G ────────┼─ Route A (GenericDecomp) ──────── acoplada a F
                    │
                    ├─ Route C (menores/brambles) ───── OPEN (cotas inf.)
                    │
                    └─ Plantillas 6/7 nodos c8 ─────── PARKED (RI imposible width≤4)
```

### 3.4 Arquitectura del laboratorio completo

```text
┌─────────────┐     ┌──────────────┐     ┌─────────────────┐
│  Frontend   │────▶│  FastAPI     │────▶│  Solvers / gens │
│  React/Vite │     │  backend/api │     │  reductions     │
└─────────────┘     └──────┬───────┘     └────────┬────────┘
                           │                      │
                           ▼                      ▼
                    ┌──────────────┐     ┌─────────────────┐
                    │ Conjectures  │     │ Experiments     │
                    │ Barriers     │     │ CSV / JSON E2   │
                    │ ProofAuditor │     │                 │
                    └──────────────┘     └─────────────────┘
                           │
                           ▼
                    ┌──────────────┐     ┌─────────────────┐
                    │ lean/PNPLab  │     │ portable_cpu/   │
                    │ ChordWidth…  │     │ farm resumible  │
                    └──────────────┘     └─────────────────┘
```

Más detalle: [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md).

---

## 4. Mapa del repositorio

| Ruta | Rol |
|------|-----|
| `backend/` | Modelos CNF, solvers, generadores, proof complexity, API |
| `lean/PNPLab/` | Formalización Lean 4 (ChordWidth, Tseitin, …) |
| `scripts/` | Treewidth, verify_chord_treewidth, búsqueda de contraejemplos |
| `portable_cpu/` | Jobs CPU con checkpoint/log (Ubuntu) |
| `reports/` | Auditorías, matrices de rutas, resultados E2 |
| `experiments/` | Artefactos JSON/CSV reproducibles |
| `frontend/` | Dashboard React (experimentos SAT / complejidad) |
| `docs/` | Metodología y arquitectura |
| `conjectures/` | Base de conjeturas |
| `SECURITY.md` | Política de secretos / privacidad |

---

## 5. Niveles de evidencia

| Nivel | Significado |
|------:|-------------|
| E0 | Idea informal |
| E1 | Observación en ejemplos |
| E2 | Evidencia computacional reproducible |
| E3 | Conjetura bien formulada |
| E4 | Prueba manual parcialmente revisada |
| E5 | Prueba formal verificada en Lean |
| E6 | Revisión externa especializada |

**Política:** E2 ≠ teorema. Este repo etiqueta honestamente lo OPEN.

---

## 6. Quick start

### 6.1 Python (laboratorio + experimentos)

```bash
python -m venv .venv
# Windows: .venv\Scripts\activate
# Unix:    source .venv/bin/activate
pip install -e ".[dev]"
pytest

# Treewidth exacto n=5..14 (largo)
python scripts/verify_chord_treewidth.py --n-lo 5 --n-hi 14 --no-representative \
  --exact-max-nodes 32 --csv reports/chord_treewidth_exact_n5_n14.csv

# Búsqueda de contraejemplos
PYTHONPATH=scripts python scripts/chordwidth/search_two_chord_counterexamples.py \
  --n-lo 5 --n-hi 14 --memory-safe
```

### 6.2 Lean (ChordWidth)

```bash
cd lean
lake exe cache get
lake build PNPLab.ChordWidth.Main
```

### 6.3 Farm CPU (Ubuntu, high-RAM)

```bash
bash portable_cpu/bin/setup_ubuntu.sh
bash portable_cpu/bin/run_all.sh --profile high_ram --resume
```

### 6.4 Dashboard

```bash
uvicorn backend.api.main:app --reload --port 8000
cd frontend && npm install && npm run dev
# http://localhost:5173
```

---

## 7. Pendientes de investigación (honestos)

| Área | Estado | Notas |
|------|--------|-------|
| G1 ∀n | OPEN | Crítico; necesita discharge paramétrico + cotas inferiores |
| Standard-adj GenericDecomp en c8 | OPEN | 6/10 edges junction-overlap fallan preconnected |
| Hub placement paramétrico | OPEN | Diseño + Lean (no solo smokes) |
| Sweeps TW n≥15 | PENDIENTE farm | `portable_cpu` jobs |
| G2 / G5 | OPEN | Fuera del camino crítico G1 |
| Publicación del repo | **Después** | Ahora **privado** |

Los “pendientes” de prueba Lean **no se cierran con más smokes**; requieren trabajo paramétrico documentado en la matriz de rutas.

---

## 8. Privacidad y publicación

- El repositorio se mantiene **privado**.
- No deben existir tokens, `.env`, ni rutas absolutas personales en el árbol versionado (ver [`SECURITY.md`](SECURITY.md)).
- Logs locales de build (con paths de máquina) están en `.gitignore`.
- Cuando se decida hacerlo público: revisar `gh repo edit --visibility public` **solo tras** una pasada de secret scanning.

---

## 9. Cómo citar / reproducir el estudio de IA

Para reproducir el **núcleo empírico** del estudio:

1. Correr la sección 6.1 (TW exacto + contraejemplos) y comparar con `reports/` y `experiments/`.
2. Leer `reports/CHORDWIDTH_AI_FINAL_REPORT.md` y `reports/CHORDWIDTH_PROOF_ROUTE_MATRIX.md`.
3. Compilar ChordWidth (sección 6.2) y verificar ausencia de `sorry` en `lean/PNPLab/ChordWidth/`.

Cualquier afirmación del tipo “la IA demostró G1” es **falsa** con el estado actual: la clasificación correcta es **PARTIAL FORMAL PROGRESS**.

---

## 10. Licencia y alcance

Herramienta de investigación y documentación de un estudio sobre asistencia de IA en prueba formal. No reclama resolución del problema del milenio P vs NP.
