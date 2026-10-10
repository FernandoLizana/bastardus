# Tree decomposition certificates

Certificados JSON verificados para grafos línea de ChordWidth (smokes + familia asintótica).

## Smokes (10/10)

Generado por `scripts/export_tree_decomp_certificate.py`. Lean: `emit_lean_tree_decomp_smokes.py` → `HasTreeDecomp` en build.

| instance | tw | decomp width | |V(L(G))| | bags |
|----------|----|--------------|---------|------|
| c5Ofold_crossing | 4 | 4 | 7 | 7 |
| c6Crossing_crossing | 4 | 4 | 8 | 8 |
| c7Crossing_crossing | 4 | 4 | 9 | 9 |
| c7Nested_noncrossing | 3 | 3 | 8 | 8 |
| c8Nested_noncrossing | 3 | 3 | 10 | 10 |
| c8Crossing_crossing | 4 | 4 | 10 | 10 |
| c9Crossing_crossing | 4 | 4 | 11 | 11 |
| c9Nested_noncrossing | 3 | 3 | 10 | 10 |
| c10Crossing_crossing | 4 | 4 | 12 | 12 |
| c10Nested_noncrossing | 3 | 3 | 11 | 11 |

## Asintótico (cubic Hamiltonian D_n)

Generado por `scripts/export_asymptotic_tree_decomp_certificates.py`. Detalle en [`asymptotic/README.md`](asymptotic/README.md).

| n | tw | decomp width | |V(L(G))| | Lean certified |
|---|----|--------------|---------|----------------|
| 6 | 5 | 5 | 9 | yes |
| 8 | 5 | 5 | 12 | yes |
| 10 | 5 | 5 | 15 | yes |
| 12 | 6 | 6 | 18 | JSON only |
| 14 | 7 | 7 | 21 | JSON only |

n≥12: tw heurístico (|V(L)| > 14, fuera de búsqueda exacta Python bitset).

## Regeneración

```powershell
$env:PYTHONPATH="scripts"
python scripts/export_tree_decomp_certificate.py
python scripts/export_asymptotic_tree_decomp_certificates.py
python scripts/emit_lean_tree_decomp_smokes.py
python scripts/emit_lean_tree_decomp_asymptotic.py
cd lean; $env:LEAN_NUM_THREADS="2"; lake build PNPLab.ChordWidth.Main
```

Optional: `LIBTW_JAR=/path/to/libtw.jar` + `scripts/libtw_adapter.py` (Java no requerido).
