# ChordWidth → P≠NP Research Program (first delivery)

**Commit reproducible:** working tree (git sin commits en este clon; pin Mathlib `v4.32.0` en `lean/lakefile.toml`).

**Disclaimer:** Este programa **no demuestra ni se acerca a P≠NP**. El caso base dos acordes (ancho 3/4) es **estructura finita**; no implica cotas inferiores superpolinomiales.

## Mapa de archivos Lean

| Ruta | Rol |
|------|-----|
| `PNPLab/ChordWidth/Main.lean` | Entry point aislado (`lake build PNPLab.ChordWidth.Main`) |
| `PNPLab/ChordWidth/TreeDecomp/Basic.lean` | `TreeDecomp`, `HasTreeDecomp` (vendored fiel PR #38334) |
| `PNPLab/ChordWidth/TreeDecomp/Smoke.lean` | Certificados K₄ / C₄ |
| `PNPLab/ChordWidth/Treewidth.lean` | `TreewidthCertificate`, `ExperimentalTreewidthBound` |
| `PNPLab/ChordWidth/ChordDiagram.lean` | `ChordDiagram n k`, `underlyingGraph`, `lineGraph` |
| `PNPLab/ChordWidth/IntersectionGraph.lean` | `intersectionGraph`, cruce en C_n |
| `PNPLab/ChordWidth/TopologicalCore.lean` | theta / fourBranch / degenerate |
| `PNPLab/ChordWidth/GeneralTseitin.lean` | Tseitin grafo arbitrario + φ impar |
| `PNPLab/ChordWidth/BaseCaseTwoChords/*` | Caso k=2 movido (pruebas preservadas) |
| `PNPLab/ChordWidth/LiteratureHypothesis.lean` | Hipótesis Galesi et al. (sin campo circular tw) |

Re-exports en rutas antiguas (`CycleTwoChords.lean`, etc.) apuntan a `BaseCaseTwoChords/`.

## Fases entregadas

- **Phase 0:** sin `TreewidthWitness` basado en `True`; descomposición real; base k=2 reubicada.
- **Phase 1:** diagramas k-cuerda + intersección + núcleo topológico.
- **Phase 2:** `scripts/scan_chord_treewidth_relations.py` + CSV + reporte.
- **Phase 3:** familia candidata documentada (Hamiltoniano cúbico + emparejamiento).
- **Phase 12 (parcial):** `reports/P_NE_NP_DEPENDENCY_GRAPH.md`.

## Build aislado

```bash
cd lean && set LEAN_NUM_THREADS=2 && lake build PNPLab.ChordWidth.Main
```

No importar en `PNPLab.lean` raíz. No `lake build PNPLab` completo (OOM).

## Dependencias

- Mathlib `v4.32.0` (sin `SimpleGraph.treeWidth` upstream).
- Python 3 + NetworkX para escaneos.

## Distancia explícita a P≠NP

1. Sin teorema `tw(L(G_n)) = Ω(n^α)` formalizado (solo candidatos + datos).
2. Sin reducción SAT → familia ChordWidth verificada en Lean.
3. Barreras clásicas (relativización, natural proofs) no abordadas.
4. Ancho de resolución finito en Δ=3 **no** escala a superpolinomial.

**Próximo teorema mínimo:** smokes 10/10 + asintótico n=6,8,10 `HasTreeDecomp` **DONE** (JSON n=12,14). Siguiente: tw(L(G))=3/4 ∀n combinatorio o cert Lean n≥12.
