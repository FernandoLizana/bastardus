# ChordWidth AI Baseline Audit

**Date:** 2026-08-04  
**Branch:** `research/chordwidth-universal-ai`  
**Commit:** none (repo sin commits iniciales)  
**Lean:** v4.32.0 | **Mathlib:** v4.32.0 (`lean/lakefile.toml`)  
**Build:** `lake build PNPLab.ChordWidth.Main` → **1271/1271 jobs SUCCESS**

---

## 1. Archivos clave

| Archivo | Rol |
|---------|-----|
| `lean/PNPLab/ChordWidth/BaseCaseTwoChords/CycleTwoChords.lean` | `CycleTwoChordGraph`, crossing/noncrossing, `toSimpleGraph` |
| `lean/PNPLab/ChordWidth/BaseCaseTwoChords/DegreeBounds.lean` | `isDelta3Admissible`, `isNondegenerate`, degeneración |
| `lean/PNPLab/ChordWidth/BaseCaseTwoChords/DegreeTwoSuppression.lean` | `SuppressedCore`, supresión grado 2 |
| `lean/PNPLab/ChordWidth/BaseCaseTwoChords/TwoChordCore.lean` | `isK4` / `isFourCycle` **estructural** (no iso) |
| `lean/PNPLab/ChordWidth/TreeDecomp/Basic.lean` | `TreeDecomp`, `HasTreeDecomp`, width = \|bag\|−1 |
| `lean/PNPLab/ChordWidth/Treewidth.lean` | `TreewidthCertificate`, `LineGraphTwBound certified\|experimental` |
| `lean/PNPLab/ChordWidth/BaseCaseTwoChords/Laws/*.lean` | Width condicional por smoke |
| `lean/PNPLab/ChordWidth/BaseCaseTwoChords/TseitinEncoding.lean` | Encoder noncrossing paramétrico; crossing vía `CrossingEndpoints` |
| `lean/PNPLab/ChordWidth/LiteratureHypothesis.lean` | Hipótesis Galesi (structure, no teorema) |
| `lean/PNPLab/ChordWidth/BaseCaseTwoChords/CycleTwoChords/MainTheorem.lean` | Teorema **condicional** por instancia |
| `scripts/verify_chord_treewidth.py` | Barrido tw exacto/representativo |
| `scripts/chordwidth/search_two_chord_counterexamples.py` | Búsqueda adversarial (nuevo) |

---

## 2. Definiciones exactas de gaps

### G1 — Dicotomía universal tw(L(G))

**Enunciado objetivo:**

- `¬ crossing ∧ válido` → `tw(L(G)) = 3`
- `crossing ∧ válido` → `tw(L(G)) = 4`

**Estado:** **OPEN**

**Evidencia existente:** COMPUTATIONALLY VERIFIED n=5..14 (2870 configs Δ=3); finitos Lean `HasTreeDecomp` en smokes 10/10 + asintótico n=6,8,10. **No cuantifica ∀n.**

### G2 — Núcleo estructural

**“Núcleo” en repo:** `SuppressedCore` (`DegreeTwoSuppression.lean`) = conjunto `branchVertices` (vértices grado ≠ 2) + longitudes de caminos suprimibles.

**`isK4`:** 4 branch vertices, 6 aristas `branchSuppressAdjacent` — **NO** `SimpleGraph.Iso` a `⊤ : SimpleGraph (Fin 4)`.

**`isFourCycle`:** 4 branch vertices, grado suppress 2, 4 aristas — **NO** iso a `cycleGraph 4`.

**Estado:** **OPEN** para ∀n; **PROVED** en smokes vía transporte a `c5SmokeGraph`/`c8SmokeGraph`.

**Salto informal:** de núcleo suppress-adjacency a `tw(L(G))` no formalizado universalmente.

### G5 — Tseitin crossing paramétrico

**Noncrossing:** `tseitinAxiomsNoncrossingFromMarking` — paramétrico en endpoints.

**Crossing:** `toCrossingEndpoints` → `CrossingEndpoints.tseitinAxioms` (módulo externo `PNPLab.CrossingEndpointsTseitin`).

**Estado:** **OPEN** — crossing no simétrico; `TwoChordWidthContext` exige `TseitinWidthTreewidthCharacterization` como **hipótesis**, no la demuestra.

---

## 3. Tabla de teoremas principales

| Teorema | Clasificación | Universal |
|---------|---------------|-----------|
| `cycle_two_chords_resolution_width_conditional` | CONDITIONAL | No (por instancia + `TwoChordWidthDichotomy`) |
| `width_from_treewidth_of_characterization` | CONDITIONAL | Sí (dado char Galesi) |
| `c5OfoldGraph_lineGraph_hasTreeDecomp_four` | PROVED (finito) | No |
| Smokes c6–c10 `.certified` | PROVED (finito) | No |
| `cyclicGaps_sum` (ArcLengths) | PROVED | **Sí** (nuevo) |
| `isNondegenerate → realMaxDegreeThree` (nested) | PROVED | Parcial (nested) |
| `SuppressedCore.isK4` smoke transport | PROVED (finito) | No |

---

## 4. Placeholders Lean (ChordWidth)

| Patrón | Count en `.lean` ChordWidth |
|--------|----------------------------|
| `sorry` | **0** |
| `admit` | **0** |
| `axiom` local | **0** |
| `native_decide` | Certificados finitos (`Certificates*.lean`, `CertPathGraph*.lean`) |
| `ExperimentalTreewidthBound` | Fallback cuando no hay certificado |

---

## 5. Riesgos detectados

1. **`maxDegree_eq_three` vs `realMaxDegreeThree`:** el primero solo exige `4 ≤ n`; el segundo es Δ=3 real. `TwoChordWidthContext` usa el proxy débil.
2. **`isK4` ≠ isomorfismo K₄:** G2 documentado como “core” pero no es clasificación gráfica completa.
3. **Pairing `disjoint`:** incluido en noncrossing Python; puede ser degenerado (Δ<3).
4. **Documentación vs código:** algunos informes decían 1077 jobs; build actual 1271.
5. **Conjetura no refutada** en n≤14 exacto previo; nuevo script mezcla heurística en |V(L)|>14 dentro del rango n=5..14 para algunos configs.

---

## 6. Divergencias doc ↔ código

- `CHORDWIDTH_MASTER_ARTIFACT.md` §2 aún lista “stubs tw” — parcialmente obsoleto (certificados reales existen).
- Galesi citado como literatura; `TseitinWidthTreewidthCharacterization` es **structure** asumida por usuario de teorema condicional.

---

## 7. Rutas de prueba propuestas (prioridad)

1. **Ruta F (pathwidth):** descomposición en camino explícita noncrossing — ver `notes/proofs/noncrossing_path_decomp_sketch.md`
2. **Ruta A:** bags deslizantes sobre arcos cíclicos (`ArcLengths.lean` base)
3. **Ruta C:** cotas inferiores vía menor en L(G) (K₄ o TW4 minor)
4. **Ruta D:** subdivisión + lema L(H') vs L(H)

---

## 8. Comandos baseline

```powershell
cd lean
$env:LEAN_NUM_THREADS="2"
lake build PNPLab.ChordWidth.Main

cd ..
$env:PYTHONPATH="scripts"
python scripts/chordwidth/search_two_chord_counterexamples.py --n-lo 5 --n-hi 14 --memory-safe
```
