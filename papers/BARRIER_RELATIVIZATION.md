# Barrera de relativización

## Qué dice la barrera

Si una prueba de separación usa solo argumentos **invariantes bajo extensiones de oráculo**,
entonces no puede probar **P ≠ NP** (Baker–Gill–Solovay, 1975).

Existen oráculos `A`, `B` tales que:

- **P^A = NP^A** (relativizado, P = NP)
- **P^B ≠ NP^B** (relativizado, P ≠ NP)

Cualquier técnica que funcione igual con cualquier oráculo no puede distinguir los dos mundos.

## Relevancia para width / resolución

Los **lower bounds de ancho de resolución** para fórmulas Tseitin concretas:

- Son propiedades de un **objeto finito fijo** (CNF, grafo, carga).
- **No** se formulan naturalmente como separación relativizada P vs NP.
- No compiten directamente con la barrera: no son candidatos a “prueba de P≠NP vía oráculo”.

## Por qué el lab bastardus no la viola (ni la esquiva)

| Aspecto | Estado |
|---------|--------|
| Objetivo declarado | Width vs Δ en Tseitin restringido (Category C/D) |
| Claim-gate Camino B | **Bloqueado** (`restricted_model`, `b_not_method_specific`) |
| Uso de oráculos | Ninguno en el motor de prueba |

## Implicación honesta

Incluso si se demostrara una ley completa “cruce ⇔ Width > Δ” para familias outerplanar/bicyclic,
eso **no** implica P ≠ NP salvo un puente adicional no presente en este repositorio.

## Referencias internas

- `docs/P_VS_NP_CLAIM_GATE.md`
- `papers/ROADMAP_P_VS_NP.md`
- `papers/WHY_WIDTH_IS_NOT_P_NE_NP.md`
