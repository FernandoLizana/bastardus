# Theorem dossier: TD-TSEITIN-WIDTH-TREES-001

## What is claimed / not claimed

**Claimed (target promotion R4–R5):** a weak lemma on Tseitin resolution width for trees and cycles.

**Not claimed:** P≠NP, novelty of expander lower bounds, improvement of JAIR 2023 regular-resolution characterization, or a mid-range general-resolution size theorem.

---

## 1. Result concreto más prometedor

Dos productos del sprint:

1. **Refutación certificada (valiosa):** la conjetura “Width = Δ siempre” es falsa; existen grafos 3-regulares con n=6 y Width ∈ {4,5}.
2. **Lema débil superviviente:** para árboles (y ciclos) con carga de paridad total impar, Width(T(G,c)) = Δ(G).

El lema débil es el único candidato a teorema; la refutación es el resultado negativo más sólido.

---

## statement.md

### Nombre
**Weak Exact Width for Tree Tseitin Formulas**

### Objetos
Grafos no dirigidos finitos simples; fórmulas Tseitin; ancho mínimo de resolución.

### Parámetros
Árbol T=(V,E), Δ=máx grado, carga c:V→{0,1}.

### Hipótesis
T es un árbol conector (|V|≥2), ∑_v c(v) ≡ 1 (mod 2).

### Conclusión
El ancho mínimo de una refutación por resolución de la fórmula Tseitin T(T,c) (codificación CNF estándar de XOR por vértice) es exactamente Δ(T).

### Cuantificadores
∀ árboles T con |V|≥2, ∀ c:V→{0,1} con suma impar, Width(T(T,c)) = Δ(T).

### Caso base
|V|=2: un único eje e; cargas (1,0) o (0,1) ⇒ cláusulas unitarias opuestas tras reducción ⇒ Width=1=Δ.

### Asintótica
Afirmación exacta para todo n, no solo asintótica.

### Resultado conocido más cercano
BSW / Urquhart / JAIR 2023 tratan expanders y treewidth asintótico; no necesitamos esos para árboles (tw=1). Alekhnovich–Razborov dan cotas 2^{O(tw)} de tamaño. La igualdad exacta Width=Δ en árboles parece **elemental / posiblemente folklórica** — no la anunciamos como gran novedad.

### Diferencia exacta con la literatura
Aporta (si se completa la prueba) una identidad exacta trivial-pero-limpia + certificados computacionales independientes, no una cota expansora nueva.

---

## definitions.md

- **Tseitin:** variable por arista; por vértice v, XOR de aristas incidentes = c(v).
- **UNSAT** en componentes conexas ⇔ suma de cargas impar.
- **Width** de una refutación: máx número de literales en cláusula de la prueba.
- **Width(F):** mínimo width sobre refutaciones por resolución (sistema estándar).

---

## experimental_evidence.md

Stage A (`backend.proof_complexity.pilot`): 64 instancias, Δ≤3.

- Todos los árboles y ciclos: Width=Δ (ciclos: Δ=2 ⇒ Width=2).
- Contrajemplos a Width=Δ global: 3-regulares n=6,8.

Evidence ≤ **E2** para datos; el lema aspira a **R4/R5** vía prueba.

---

## counterexample_search.md

Búsqueda diseñada para destruir Width=Δ:

- árboles aleatorios, caminos, ciclos, grids 2×k, two-cycles+bridge, 3-regulares.

Resultado: destruida globalmente; intacta en árboles/ciclos del piloto.

Holdout futuro: estrellas, árboles path-like, n≤20 con Δ≤4 (si el oráculo de width escala).

---

## proof_attempt.md

### Lower bound
Toda refutación tiene width ≥ ancho de axioma. El vértice de grado Δ genera cláusulas de ancho Δ en la codificación XOR ⇒ Width ≥ Δ.

### Upper bound (árboles) — boceto inductivo
Inducción en |V|.

Hoja ℓ unida por e={ℓ,u}, carga χ=c(ℓ). El XOR de grado 1 produce la unidad que fija e=χ.
Sustituir e en el XOR de u reduce el grado efectivo; el árbol T'=T−ℓ con carga actualizada en u sigue con suma impar.
Por inducción, T' tiene refutación de width ≤ Δ(T') ≤ Δ(T).
Las unidades y la sustitución se simulan por resolución sin superar width Δ.

**Primer paso no escrito con rigor pleno:** el lema de sustitución “restringir una variable en la CNF de un XOR de aridad ≤Δ y simular la inducción dentro de resolución preservando width ≤Δ”.

### Ciclos
Δ=2. Tras eliminar un camino de unidad-propagación / resolución binaria alrededor del ciclo, la inconsistencia de paridad produce □ con width 2.

---

## barrier_analysis.md

Relativización / natural proofs / algebrization: **no aplican** — no intentamos P≠NP.
El resultado vive enteramente en resolución (sistema restringido).

Automatizability: no se afirma un algoritmo polinómico para SAT.

---

## formalization_status.md

Lean: definiciones Tseitin/XOR y lema Width≥Δ (axiomático) + casos |V|=2.
Inducción completa: pendiente (E5 parcial).

---

## known_weaknesses.md

1. Posible folklore no acreditado sin survey exhaustivo de notas de curso.
2. Codificación XOR CNF es la estándar 2^{d-1}; otra codificación cambiaría el ancho de axioma.
3. tw_upper heurístico no debe usarse en conjeturas de cotas inferiores.
4. El piloto excluyó Δ>3 por coste de saturación.

---

## reproducibility.md

```bash
python -c "from backend.proof_complexity.pilot import run_pilot; run_pilot()"
python -c "from backend.proof_complexity.tseitin_family import make_random_regular,tseitin_cnf; from backend.proof_complexity.width import min_resolution_width; print(min_resolution_width(tseitin_cnf(make_random_regular(6,3,seed=1))))"
```

---

## review_questions.md

1. ¿Existe referencia primaria que enuncie Width=Δ para Tseitin en árboles?
2. ¿El lema de sustitución XOR→resolución está en algún survey?
3. ¿Debemos publicar solo la refutación computacional + tabla exacta n≤8?
