# Escala Lean vs masa E2 (bicyclic / Whitney)

## Por qué no hay pack Lean C₁₂+chord

| Instancia | \|Closure₃\| | Lean `native_decide` |
|-----------|--------------|----------------------|
| C₄+chord | 131 | OK (`BicyclicWidth3`) |
| C₅+chord | 233 | OK (`BicyclicC5Width3`) |
| C₆+chord | ~379 | OK (`BicyclicC6Width3`) |
| C₁₂+chord | **~2627** | Impracticable (ClosedUnder ∈ O(\|S\|²·\|pivots\|)) |

E2: `bicyclic_full_closure_mass.json` — **48/48** incluye todos los Cₙ+chord n≤12
con □ ∈ Closure_Δ.

## Whitney / tip-existence

Lean actual (`Outerplanar.lean`):

- `earLaw` sigue siendo **campo axiomatizado** del sketch
- Lemas: `tipExists_of_not_cycle`, `tip_or_cycle_of_earLaw`
- Instancias: `whitney_triangle_instance`, `whitney_shortcut_instance`

Para descargar el axioma haría falta Mathlib graph theory (ear decomposition)
o un modelo combinatorio finito de grafos outerplanar Δ≤3.

## Política del lab

1. Packs Lean: instancias con \|Cl\| ≲ 500
2. Masa Python: n grande (E2)
3. No bloquear E5 familia por saturación Lean en n=12
