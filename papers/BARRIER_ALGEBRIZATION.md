# Barrera de algebrización (Aaronson–Wigderson)

## Qué dice la barrera

La **algebrización** (Aaronson–Wigderson, 2009) extiende la crítica relativizante: muchas
técnicas que incluyen estructura algebraica sobre oráculos (polinomios, extensiones de campo)
siguen siendo incapaces de resolver separaciones clásicas.

Intuición: si un argumento funciona igual al **sustituir** la función booleana por su versión
“algebrizada”, entonces está sujeto a límites similares a los de Baker–Gill–Solovay.

## Relevancia para proof complexity

Los lower bounds de **resolución**, **Frege**, **cutting planes**, etc.:

- Trabajan sobre **derivaciones sintácticas** en un cálculo fijo.
- No son, en general, pruebas algebrizantes sobre `P^O` vs `NP^O`.

Un teorema del tipo “Tseitin(G) requiere ancho ≥ w” es una **no-existencia de derivación** con
ancho acotado — categoría distinta de separación de clases relativizadas.

## Width vs Δ en este repo

El motor Python/Lean:

- Enumera / decide membresía en `Closure_w` para instancias **finitas**.
- No construye extensiones algebraicas de oráculos.
- Por tanto **no está diseñado** para evadir o atacar la barrera de algebrización.

## Puente hipotético (no presente)

Para conectar width a P≠NP haría falta algo como:

> Familia de CNFs `{φ_n}` con reducción Karp desde SAT, y lower bound de ancho superpolinomial
> en **todo** cálculo de prueba que simule P.

Eso es **mucho más fuerte** que los certificados Category C actuales.

## Conclusión

La algebrización refuerza la postura del claim-gate: el trabajo Width/Δ es **combinatoria de
pruebas**, no separación de complejidad algebrizante.

## Referencias

- Aaronson, Wigderson — *Algebrization* (TOCT 2009)
- `papers/BARRIER_RELATIVIZATION.md`
- `papers/WHY_WIDTH_IS_NOT_P_NE_NP.md`
