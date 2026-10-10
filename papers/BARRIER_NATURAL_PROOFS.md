# Barrera de pruebas naturales (Razborov–Rudich)

## Qué dice la barrera

Muchas técnicas “naturales” para circuit lower bounds (aproximaciones, interpolantes, ciertos
grados en sistemas de prueba) están limitadas por **Natural Proofs** (Razborov–Rudich, 1997):

- Si una propiedad de funciones es **constructiva** (eficientemente reconocible) y **amplia**
  (cubre muchas funciones aleatorias), entonces no puede ser **muy útil** para demostrar lower
  bounds fuertes, salvo colapsos criptográficos.

## Relevancia para resolución / width

- Los resultados de **ancho mínimo de resolución** (Ben-Sasson, Wigderson, etc.) son
  **lower bounds sobre un modelo de prueba**, no sobre circuitos generales.
- Demostrar que una familia concreta de Tseitin requiere ancho ≥ k en resolución es un
  teorema **finito-combinatorio** sobre derivaciones; no es automáticamente una “propiedad
  natural” en el sentido Razborov–Rudich sobre funciones booleanas aleatorias.

## Riesgo de malinterpretación

Confundir:

1. “Esta familia Tseitin necesita ancho 4 en resolución”  
2. “SAT es difícil en general / P ≠ NP”

El (1) no implica (2) sin un puente de **hardness de SAT** en el sentido clásico.

## Posición del lab

| Trabajo | ¿Natural proof hacia P≠NP? |
|---------|---------------------------|
| Packs `K4Width3`, proyecciones | No — certificados finitos |
| Masa 461/461 multihop | No — verificación empírica |
| γ/Δ map | No — fenomenología width |

## Conclusión

La barrera de pruebas naturales **no bloquea** el programa Width vs Δ; solo advierte que
**no debe venderse** como ataque a P vs NP.

## Referencias

- Razborov, Rudich — *Natural Proofs* (JCSS 1997)
- `papers/BARRIER_ALGEBRIZATION.md`
