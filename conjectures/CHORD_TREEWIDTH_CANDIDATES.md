# Chord treewidth relation candidates

Conjeturas separadas de teoremas. Generadas a partir del escaneo `scripts/scan_chord_treewidth_relations.py`.

## Conjetura CAND-TW-01 (caso k=2, no cruce)

Para G = C_n + dos acordes no cruzantes válidos (Δ=3, no degenerados):

```
tw(L(G)) = 3
```

**Evidencia:** 1870/1870 exact n=5..14 (reporte previo). **Lean:** smokes c7/c8/c9/c10 nested `.certified` en Laws.

## Conjetura CAND-TW-02 (caso k=2, cruce)

Para G cruzante válido:

```
tw(L(G)) = 4
```

**Evidencia:** 1000/1000 exact crossing n=5..14. **Lean:** smokes c5..c10 crossing `.certified` en Laws.

## Conjetura CAND-TW-03 (intersección vs linea)

Para k=2:

```
tw(I(D)) ≤ tw(L(D))   ? 
tw(I(D)) = 1  ⟺  cruce   (I es K_2 o 2K_1)
```

**Estado:** verificar en CSV; contraejemplos se listan en scan report.

## Conjetura CAND-TW-04 (familia asintótica)

Grafos hamiltonianos cúbicos H_n = C_n + emparejamiento perfecto de cuerdas (construcción determinística).

```
tw(L(H_n)) ≥ c · n   (ideal α=1)
```

**Estado:** candidato numérico; **sin** prueba Lean ∀n. JSON en `reports/tree_decomp_certificates/asymptotic/` (n=6..14); Lean `HasTreeDecomp` solo **n=6**. Ver `experiments/asymptotic_cubic_hamiltonian_tw.csv`.

## No emitir como axiomas Lean

Estos enunciados permanecen en markdown/CSV hasta certificación `HasTreeDecomp` o teorema de cota inferior.
