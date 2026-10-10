# Asymptotic cubic Hamiltonian tree-decomposition certificates

Generado por `scripts/export_asymptotic_tree_decomp_certificates.py`.

Familia: C_n + cuerdas (i, i+n/2) para n par; certificado sobre L(G).

| n | tw | decomp width | |V(L(G))| | bags | tw method | Lean |
|---|----|--------------|---------|------|-----------|------|
| 6 | 5 | 5 | 9 | 9 | exact_width_search | **certified** |
| 8 | 5 | 5 | 12 | 12 | exact_width_search | **certified** |
| 10 | 5 | 5 | 15 | 15 | exact_width_search | **certified** |
| 12 | 6 | 6 | 18 | 18 | memory_guard_heuristic | JSON only |
| 14 | 7 | 7 | 21 | 21 | networkx_upper_bound | JSON only |

Lean n=6,8,10: `CertificatesAsymptotic.lean` (`set_option maxHeartbeats 1600000`).

n ≥ 12 Python: |V(L)| > 14 fuera de búsqueda exacta bitset; tw vía heurística, descomposición verificada al ancho reportado.

Regenerar:

```powershell
$env:PYTHONPATH="scripts"
python scripts/export_asymptotic_tree_decomp_certificates.py
python scripts/emit_lean_tree_decomp_asymptotic.py
cd lean; $env:LEAN_NUM_THREADS="2"; lake build PNPLab.ChordWidth.Main
```
