# P≠NP dependency graph (ChordWidth track, partial)

| ID | Enunciado | Tipo | Dependencias | Estado | Formalizado | Reproducible | Novedad revisada | Implicación hacia P≠NP |
|----|-----------|------|--------------|--------|-------------|--------------|------------------|------------------------|
| CW-DEF-01 | `TreeDecomp`, `HasTreeDecomp` | definición | PR #38334 (vendored) | completo | sí | sí | no | ninguna directa |
| CW-DEF-02 | `ChordDiagram n k` | definición | Mathlib cycleGraph | completo | sí | sí | no | ninguna |
| CW-DEF-03 | `intersectionGraph` | definición | cruce en C_n | completo | sí | sí | no | ninguna |
| CW-DATA-01 | tw(L(G)) ∈ {3,4} k=2, n≤14 | dato experimental | Python exact | validado 2870/2870 | no (Lean) | sí | no | **ninguna** (finito) |
| CW-DATA-02 | Escaneo tw(G), tw(L), tw(I) | dato experimental | scan script | n=5..10 | no | sí | no | ninguna |
| CW-HYP-01 | width(T) = max(Δ, tw(L)) | hipótesis condicional | Galesi TOCT 2020 | literatura | parcial | N/A | no | condicional |
| CW-THM-01 | `width_from_treewidth_of_characterization` | teorema formalizado | CW-HYP-01 | condicional | sí | sí | no | **no** (asume hipótesis) |
| CW-THM-02 | K₄ `HasTreeDecomp 3` | teorema formalizado | CW-DEF-01 | completo | sí | sí | no | ninguna |
| CW-THM-03 | k=2 ↔ `CycleTwoChordGraph` | teorema formalizado | CW-DEF-02, no degenerado | condicional | sí | sí | no | ninguna |
| CW-CONJ-01 | tw(L(D_n)) = Ω(n) familia cúbica | conjetura | CW-DATA-02 | abierto | no | parcial | pendiente | **potencial** (lejano) |
| CW-GAP-01 | Reducción SAT → ChordWidth | gap abierto | — | abierto | no | no | — | necesaria para P≠NP vía este track |
| CW-GAP-02 | Superpoly lower bound from width | gap abierto | proof complexity | abierto | no | no | — | barrera |

**Nota:** Ninguna fila implica P≠NP en el estado actual.
