# ChordWidth — Artefacto maestro (estado + vías de ataque)

**Generado:** 2026-08-03  
**Workspace:** `bastardus`  
**Build gate:** `lake build PNPLab.ChordWidth.Main` → **1270/1270 jobs**, sin `sorry`/`admit`/axioma propio  
**Aislamiento:** no importado en `PNPLab.lean`; track 461 casos intacto  

---

## 1. Objetivo final (no demostrado aún)

Para todo \(n \ge 5\), toda instancia válida \(G = C_n +\) dos cuerdas (4 endpoints, filtro Python \(\Delta=3\)), y toda marcación impar \(\varphi\):

\[
\mathrm{Width}(T(G,\varphi)) = 3 \iff \text{cuerdas no cruzadas}
\]

Vía literatura (Galesi–Talebanfard–Torán, TOCT 2020):

\[
\mathrm{Width}(T(G,\varphi)) = \max\{\Delta(G),\, \mathrm{tw}(L(G))\}
\]

Con \(\Delta = 3\): Width = 3 o 4 según tw(L(G)) ∈ {3, 4}.

**Teorema Lean objetivo (Fase 5):** `cycle_two_chords_resolution_width` — incondicional ∀n.

**Hoy:** `cycle_two_chords_resolution_width_conditional` — por instancia fija + hipótesis + testigos tw.

---

## 2. Resumen ejecutivo — qué está comprobado

| Capa | Estado | Evidencia |
|------|--------|-----------|
| Lean scaffold Fase 1–5 | **Verde** | 1277 jobs, NoncrossingPathDecomp blocks 1–5 + c8 Fin bridges |
| Ley condicional Width = max(3, tw) | **Demostrada** | `LiteratureHypothesis.lean` |
| Dicotomía condicional por instancia | **Demostrada** | `Dichotomy.lean`, `MainTheorem.lean` |
| Núcleo K₄/C₄ smoke | **Demostrado** | `TwoChordCore.lean` (c5/c8) |
| Δ = 3 real (no degenerado) | **Demostrado ∀g** | `DegreeBounds.lean` |
| maxDegree ≤ 3 ∀g válido | **Demostrado** | `toSimpleGraph_maxDegree_le_three_holds` |
| Tseitin φ (noncrossing) | **Cableado** | `TseitinEncoding.lean` |
| tw(L(G)) = 3/4 ∀n | **No demostrado** | stubs + Python |
| Python exacto n≤14 | **2870/2870** | 0 contraejemplos |
| Python representativo n≤100 | **383/383** | heurística n≥9 |
| Python n=15..16 | **8/8** | representativo |
| Python n=7..10 | **16/16** | sesión A4 |

---

## 3. Módulos Lean (14 archivos)

Build: `cd lean && LEAN_NUM_THREADS=2 lake build PNPLab.ChordWidth.Main`

| # | Archivo | Rol |
|---|---------|-----|
| 1 | `LiteratureHypothesis.lean` | `TseitinWidthTreewidthCharacterization`; `width_from_treewidth_of_characterization` |
| 2 | `CycleTwoChords.lean` | `CycleTwoChordGraph`, smoke c5–c10, transport maxDegree |
| 3 | `DegreeBounds.lean` | Filtro Python `isDelta3Admissible`; no degeneración; A1+A2 |
| 4 | `SimpleGraph/DegreeSup.lean` | Lemas `⊔`/`edge`/`cycleGraph` grado |
| 5 | `TseitinEncoding.lean` | Axioms, φ, `TwoChordSmokeTseitinUnification` |
| 6 | `LineGraph.lean` | Alias `SimpleGraph.lineGraph` |
| 7 | `Treewidth.lean` | `TreewidthWitness`, `EliminationOrder` (stub) |
| 8 | `DegreeTwoSuppression.lean` | Supresión grado 2, núcleo |
| 9 | `TwoChordCore.lean` | `SuppressedCore.isK4` / `isFourCycle` |
| 10 | `Laws/CrossingWidth4.lean` | Width = 4 condicional (crossing) |
| 11 | `Laws/NoncrossingWidth3.lean` | Width = 3 condicional (noncrossing) |
| 12 | `CycleTwoChords/Dichotomy.lean` | Bundle dicotomía |
| 13 | `CycleTwoChords/MainTheorem.lean` | `cycle_two_chords_resolution_width_conditional` |
| 14 | `Main.lean` | Entry + `TwoChordWidthContext.ofSmokeUnification` |

---

## 4. Teoremas Lean clave (por módulo)

### 4.1 LiteratureHypothesis
- `TseitinWidthTreewidthCharacterization` — structure (hipótesis Galesi)
- `width_from_treewidth_of_characterization` — Width = max(Δ, k) dado tw = k
- `two_chord_width_from_characterization` — especialización Δ = 3
- `noncrossing_width_eq_three_when_tw_le_two` / `when_tw_eq_three`

### 4.2 CycleTwoChords
- `CycleTwoChordGraph` — n, p0<p1<p2<p3, pairing (crossing|nested|disjoint)
- `toSimpleGraph` — crossing → `CrossingEndpoints`; else encoder noncrossing
- `toSimpleGraph_eq_noncrossing` — forma uniforme `cycleGraph ⊔ edge ⊔ edge`
- Smoke: **c5Ofold, c6Crossing, c7Crossing, c7Nested, c8Crossing, c8Nested, c9Crossing, c9Nested, c10Crossing, c10Nested**
- `realMaxDegreeThree_of_graph_eq` — transport smoke + `native_decide`

### 4.3 DegreeBounds (A1+A2 — cerrado 2026-08-03)
- `isDelta3Admissible` ↔ `realMaxDegreeThree` (= Python `is_valid_delta3`)
- `chordIsCycleEdge` — cuerda ya es arista del ciclo
- `isNondegenerate` — ninguna cuerda subsumida
- `crossing_isNondegenerate` — **demostrado**
- `toSimpleGraph_maxDegree_le_three_holds` — **∀g válido, maxDegree ≤ 3**
- `isNondegenerate_implies_realMaxDegreeThree` — **demostrado**
- `crossing_isDelta3Admissible` — corolario
- Degeneración: nested si `p2 = p1+1`; disjoint si `p1 = p0+1` → maxDegree puede ser 2

### 4.4 DegreeSup
- `degree_sup_sup_le_add`, `degree_le_degree_sup`
- `cycleGraph_degree_eq_two_of_four_le`
- Lemas grado en `edge` / `⊔`

### 4.5 TseitinEncoding
- `CycleTwoChordGraph.tseitinAxioms` — crossing reusa `CrossingEndpoints`
- `tseitinFromMarking` / `oddChargeFromMarking` — rama noncrossing con φ
- `tseitinFromMarking_default` — compat legacy (carga p0)
- `TwoChordSmokeTseitinUnification` — c5, c6, c7–c10 crossing/nested
- `c5OfoldGraph_tseitinAxioms_eq_ofold` (= `ofoldGAxioms`)

### 4.6 TwoChordCore (Fase 3)
- `c5Ofold_crossing_core_k4` — núcleo K₄ smoke
- `c8Nested_noncrossing_core` — núcleo C₄ smoke
- **Gap:** no `SimpleGraph.Iso` universal a K₄/C₄

### 4.7 Laws + MainTheorem (Fase 4–5 condicional)
- `crossing_width_eq_four` — dado tw = 4 + literatura
- `noncrossing_width_eq_three_when_tw_eq_three`
- `two_chord_width_dichotomy_conditional`
- `cycle_two_chords_resolution_width_conditional`

### 4.8 Main
- `TwoChordWidthContext`
- `TwoChordWidthContext.ofSmokeUnification`
- `two_chord_width_from_characterization_of_delta3`

---

## 5. Instancias smoke (Δ = 3 verificado)

| Grafo | n | Endpoints | Pairing | Tseitin unif. |
|-------|---|-----------|---------|---------------|
| c5Ofold | 5 | 0,1,2,3 | crossing | sí |
| c6Crossing | 6 | 0,1,2,3 | crossing | sí |
| c7Crossing | 7 | 0,1,2,3 | crossing | sí |
| c7Nested | 7 | 0,1,2,3 | nested | sí |
| c8Crossing | 8 | 0,1,2,3 | crossing | sí |
| c8Nested | 8 | 0,2,4,6 | nested | sí |
| c9Crossing | 9 | 0,1,2,3 | crossing | sí |
| c9Nested | 9 | 0,2,3,5 | nested | sí |
| c10Crossing | 10 | 0,1,2,3 | crossing | sí |
| c10Nested | 10 | 0,1,2,3 | nested | sí |

---

## 6. Validación Python (comprobada, no prueba Lean)

### 6.1 Exacto n = 5..14 (2870 configs, gap-pattern, Δ=3)

| Geometría | tw(L(G)) | count |
|-----------|----------|------:|
| noncrossing | 3 | 1870 |
| crossing | 4 | 1000 |

**2870/2870**, 0 contraejemplos, ~17 min.  
Script: `scripts/verify_chord_treewidth.py --n-lo 5 --n-hi 14 --no-representative --memory-safe`  
Reporte: `reports/CHORD_TREewidth_EXACT_N5_N14.md`

### 6.2 Representativo n = 5..100 (383 configs)

**383/383**, ~14 s.  
366 configs usan `networkx_upper_bound` (n≥9); 17 exactos n≤8.  
Reporte: `reports/CHORD_TREewidth_VERIFICATION.md`

### 6.3 Extensiones sesión

| Rango | Modo | Resultado |
|-------|------|-----------|
| n=7..10 | representative | 16/16 |
| n=15..16 | representative | 8/8 |

### 6.4 Límites computacionales

- `exact_width_search` (bitset B&B): seguro hasta |V| ≤ 14 en L(G)
- n=15..20: `MemoryError` en búsqueda exacta (~18 min trial)
- Default: `--memory-safe` (skip exact si |V| > 14)

### 6.5 Filtro Δ=3 (Python = Lean)

```python
def is_valid_delta3(cfg, g):
    return max(dict(g.degree()).values()) == 3
```

Lean: `isDelta3Admissible g ↔ g.toSimpleGraph.maxDegree = 3`  
Configs degeneradas (nested/disjoint con cuerda = arista del ciclo) excluidas.

---

## 7. Lo que NO está demostrado (gaps honestos)

| ID | Gap | Impacto |
|----|-----|---------|
| G1 | tw(L(G)) = 3/4 **∀n** | Bloquea teorema universal |
| G2 | `SimpleGraph.Iso` núcleo ≅ K₄/C₄ ∀n | Fase 4b |
| G3 | Mathlib `treeWidth` | PR #38334 abierto (v4.32 pin) |
| G4 | `width_eq` desde axiomas (sin hipótesis) | Literatura char completa |
| G5 | Tseitin φ rama **crossing** | Solo noncrossing paramétrico |
| G6 | `realMaxDegreeThree` sin `isNondegenerate` | Casos Δ=2 legítimos excluidos |
| G7 | Teorema principal incondicional | Meta Fase 5 |

---

## 8. Vías de ataque (todas las alternativas)

### 8.1 Permanecer en Lean (recomendado)

| Vía | Descripción | Esfuerzo | Desbloquea |
|-----|-------------|----------|------------|
| **L-A** | Esperar/emular PR [#38334](https://github.com/leanprover-community/mathlib4/pull/38334) | 3–12 meses | tw real en Mathlib |
| **L-B** | **Vendorear** `TreeDecomp.lean` del PR en `PNPLab/ChordWidth/` | 2–5 días | tw API local ya |
| **L-C** | Witnesses `TreewidthWitness` + smoke (actual) | hecho | solo instancias |
| **L-D** | **Certificados**: Python/LibTW → JSON descomposición → Lean verifica `HasTreeDecomp` | **DONE** (smokes 10/10) | tw por instancia sin `native_decide` masivo |
| **L-E** | Elimination orders computables en L(G) smoke | 1 semana | testigos tw parciales |
| **L-F** | Port estrategia Coq TW2=K4-free (noncrossing) | 1–3 meses | rama tw=3 |
| **L-G** | Combinatoria line-graph (paper Harvey–Wood / Grohe–Marx) | investigación | argumento ∀n en papel |

### 8.2 Comunidad

| Vía | Canal | Pregunta | Tiempo usuario |
|-----|-------|----------|----------------|
| **C-Z** | Zulip #mathlib4 | ¿Vendorear #38334? ¿Pathwidth primero? | 30 min |
| **C-MO** | MathOverflow | ¿tw(L(G)) dicotomía ∀n para cycle+2 chords? | 1 h |

Archivos listos: `reports/ZULIP_MESSAGE_READY.txt`, `reports/MATHOVERFLOW_MESSAGE_READY.txt`

### 8.3 Oráculos computacionales (no prueba, certifica)

| Herramienta | Lenguaje | Rol |
|-------------|----------|-----|
| NetworkX + bitset B&B | Python | **Actual** — exacto n≤14 |
| [LibTW](https://www.treewidth.com/) | Java | TreewidthDP exacto + export TD |
| [tdlib](https://github.com/freetdi/tdlib/) | C++/Python | PACE exact algorithms |
| OGDF / Sage | C++/Py | Layout; tw indirecto |

Patrón: **compute externally → verify in Lean** (estándar SAT/ILP).

### 8.4 Otros asistentes de prueba (referencia, no migración)

| Sistema | Librería | Relevancia |
|---------|----------|------------|
| **Coq** | [rocq-community/graph-theory](https://github.com/rocq-community/graph-theory) | **Alta** — tree decompositions, **TW≤2 ⟺ K₄-free** demostrado |
| Isabelle | Flyspeck graphs | Media — planar |
| Lean otros | lambdaclass TreeDecomp checker | Parcial — verificación, no tw(L(G)) |

**No migrar a Coq** — perderías scaffold 1077 jobs; usar Coq como **guía de prueba**.

### 8.5 Track viejo (461 casos)

Intacto, verde pre-pivot. **No modificar** al expandir ChordWidth.

---

## 9. Grafo de dependencias (Fase 4–5)

```
Fase 1–2 (condicional Galesi) ──► Fase 3 (K4/C4 smoke)
         │                              │
         │                              ├──► Fase 4a: Mathlib treeWidth (#38334 o vendored)
         │                              ├──► Fase 4b: iso núcleo ∀n
         │                              ├──► Fase 4c: tw(L(G))=4 crossing
         │                              └──► Fase 4d: tw(L(G))=3 noncrossing
         │                                        │
         │                                        ▼
         │                                 Fase 4e: Width 3/4
         │                                        │
         └────────────────────────────────────────┴──► Fase 5: ∀n dichotomy
Python 2870+383 ──► evidencia (no prueba)
DegreeBounds A1+A2 ──► Δ=3 no degenerado (cerrado)
```

---

## 10. Timeline realista

| Fase | Optimista | Realista | Pesimista |
|------|-----------|----------|-----------|
| 4a Mathlib tw | 1–2 meses | 3–6 meses | 12+ meses |
| 4b–d tw(L(G)) ∀n | 2–3 meses | 4–8 meses | 12+ meses |
| 4e–f Width + φ | 1 mes | 2–4 meses | 6 meses |
| 5 teorema ∀n | 1–2 meses | 3–6 meses | 12 meses |
| **Total 4+5** | ~6 meses | **6–12 meses** | 18–24 meses |

---

## 11. Comandos de reproducción

```powershell
# Lean build (aislado)
cd lean
$env:LEAN_NUM_THREADS="2"
lake build PNPLab.ChordWidth.Main

# Python representativo n=5..100
python scripts/verify_chord_treewidth.py --n-lo 5 --n-hi 100 --representative

# Python exacto n=5..14 (~17 min)
python scripts/verify_chord_treewidth.py --n-lo 5 --n-hi 14 --no-representative --memory-safe

# Python n=15..16
python scripts/verify_chord_treewidth.py --n-lo 15 --n-hi 16 --representative

# Certificate regeneration pipeline (smokes + asymptotic family)
$env:PYTHONPATH="scripts"
python scripts/export_tree_decomp_certificate.py
python scripts/export_asymptotic_tree_decomp_certificates.py
python scripts/emit_lean_tree_decomp_smokes.py
python scripts/emit_lean_tree_decomp_asymptotic.py
# Optional LibTW (Java): set LIBTW_JAR=/path/to/libtw.jar before export
python scripts/asymptotic_cubic_hamiltonian_family.py
```

---

## 11b. Pipeline de regeneración de certificados (L-D)

| Paso | Script | Salida |
|------|--------|--------|
| 1. Smokes JSON | `scripts/export_tree_decomp_certificate.py` | `reports/tree_decomp_certificates/*.json` (10 smokes) |
| 2. Smokes Lean | `scripts/emit_lean_tree_decomp_smokes.py` | `TreeDecomp/CertificatesSmokes.lean`, `CertificatesLineSmokes.lean`, `CertPathGraphSmokes.lean` |
| 3. Asintótico JSON | `scripts/export_asymptotic_tree_decomp_certificates.py` | `reports/tree_decomp_certificates/asymptotic/*.json` (n=6,8,10,12,14) |
| 4. Asintótico Lean | `scripts/emit_lean_tree_decomp_asymptotic.py` | `TreeDecomp/CertificatesAsymptotic.lean` (n=6 certificado; n≥8 JSON-only por heartbeats) |
| 5. LibTW (opcional) | `scripts/libtw_adapter.py` | Mismo JSON si `LIBTW_JAR` apunta a jar Java; si no, fallback Python |
| 6. Escaneo tw | `scripts/asymptotic_cubic_hamiltonian_family.py` | `experiments/asymptotic_cubic_hamiltonian_tw.csv` |

**Estado L-D smoke track:** **DONE** — 10/10 smokes con `HasTreeDecomp` en Lean (build verde).

**Estado asintótico:** **Parcial** — JSON n=6..14; Lean `HasTreeDecomp` n=6,8,10 (`CertificatesAsymptotic.lean`, `maxHeartbeats 1600000`); n=12,14 solo JSON (|V(L)| > 15, tw heurístico).

**Rebuild tras regenerar Lean:**

```powershell
cd lean
$env:LEAN_NUM_THREADS="2"
lake build PNPLab.ChordWidth.Main
```

---

## 12. Inventario documentación

| Documento | Rol |
|-----------|-----|
| `CHORDWIDTH_MASTER_ARTIFACT.md` | **Este archivo** |
| `CHORDWIDTH_INTEGRATION_SUMMARY.md` | Punto de entrada |
| `CHORD_WIDTH_LEAN_STATUS.md` | Módulos + gaps |
| `SESSION_HEALTH_CHECK.md` | Health gate |
| `FASE5_ROADMAP.md` | Roadmap ∀n |
| `LITERATURE_TSEITIN_WIDTH.md` | Auditoría Galesi 2020 |
| `MATHLIB_TW_STATUS.md` | PR #38334 |
| `CROSSING_LAW_SOUNDNESS_AUDIT.md` | Soundness |
| `ZULIP_MESSAGE_READY.txt` | Post Zulip |
| `MATHOVERFLOW_MESSAGE_READY.txt` | Post MO |
| `papers/CHORD_DIAGRAM_TSEITIN_WIDTH.md` | Paper draft |

---

## 13. Recomendación priorizada (próximos 30 días)

1. **Post Zulip** (#mathlib4) — decidir vendorear #38334  
2. ~~**L-B + L-D** — TreeDecomp local + export JSON~~ → **L-D smokes DONE**; continuar asintótico n≥12  
3. **Post MathOverflow** — atajo combinatorio tw(L(G))  
4. **L-F** — leer Coq `graph-theory` (TW2, K₄-free) para rama noncrossing  
5. Mantener regression Python en cada cambio de script  

---

## 14. Disclaimer

- Python **2870/2870** y **383/383** son **evidencia computacional**, no demostración Lean ∀n.  
- La hipótesis Galesi es **literatura explícita** (`structure`), no teorema PNPLab.  
- ChordWidth **no demuestra P≠NP** — pivot estructural desde track 461 casos.  
