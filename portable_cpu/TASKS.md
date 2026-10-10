# Lista exhaustiva — trabajos CPU-intensivos

Estimaciones en **horas CPU** (≈ horas reloj × núcleos usados). Prioridad para ChordWidth/G1.

## Leyenda

| Campo | Significado |
|-------|-------------|
| **ID** | Nombre en `jobs.manifest.json` |
| **CPU h** | Horas-núcleo aproximadas |
| **Paralelo** | ¿Puede correr junto a otros? |
| **Estado repo** | Hecho / pendiente / exploratorio |

---

## A. Lean builds (alta CPU, mucha RAM)

| ID | Descripción | CPU h | Paralelo | Estado |
|----|-------------|------:|----------|--------|
| `lean_cache_get` | `lake exe cache get` (Mathlib) | 0.5–2 | no | pendiente tras clone |
| `lean_build_chordwidth` | `lake build PNPLab.ChordWidth.Main` (1278 jobs) | 2–8 | no | verde; re-validar |
| `lean_build_chordwidth_clean` | build tras `lake clean` | 4–16 | no | pendiente |
| `lean_build_genericdecomp_only` | módulo pesado solo | 1–3 | no | opcional |

**Nota:** no correr `lake build PNPLab` completo en máquinas con <32 GB RAM (OOM).

---

## B. Treewidth exacto / verificación G1 (Python) — **prioridad alta**

| ID | Descripción | CPU h | Paralelo | Estado |
|----|-------------|------:|----------|--------|
| `tw_exact_n5_n14` | Gap sweep exacto n=5..14 (2870 configs) | 0.5 | sí | hecho; re-run baseline |
| `tw_exact_n15_n18` | Gap sweep n=15..18, memory-safe | 2–6 | sí | **pendiente** |
| `tw_exact_n19_n24` | Gap sweep n=19..24 | 4–12 | sí | **pendiente** |
| `tw_exact_n25_n32` | Gap sweep n=25..32 | 8–40 | sí | **pendiente** |
| `tw_exact_n15_n24_push_exact16` | `--exact-max-nodes 16` boundary | 4–20 | sí | **pendiente** |
| `tw_exact_n15_n24_push_exact18` | `--exact-max-nodes 18` (OOM risk) | 8–40 | sí | exploratorio |
| `tw_representative_n16_n50` | Modo representative rápido | 1–4 | sí | **pendiente** |
| `tw_full_endpoints_n5_n16` | C(n,4) completo n≤16 | 4–12 | no | **pendiente** |
| `tw_crossing_focus_n10_n30` | Solo pairing crossing | 2–8 | sí | **pendiente** |
| `tw_noncrossing_focus_n10_n30` | Solo nested+disjoint | 2–8 | sí | **pendiente** |

---

## C. Búsqueda adversarial contraejemplos

| ID | Descripción | CPU h | Paralelo | Estado |
|----|-------------|------:|----------|--------|
| `cx_n5_n14` | `search_two_chord_counterexamples` n=5..14 | 0.1 | sí | hecho |
| `cx_n5_n20` | extensión n=5..20 | 0.5–2 | sí | **pendiente** |
| `cx_n5_n30` | extensión n=5..30 | 2–8 | sí | **pendiente** |
| `cx_n15_n35_exact` | exact + memory-safe n=15..35 | 10–60 | sí | exploratorio |

---

## D. Combinatoria proof-route (GenericDecomp / Route F+A)

| ID | Descripción | CPU h | Paralelo | Estado |
|----|-------------|------:|----------|--------|
| `hub_placement_search_small` | (pairing,gaps)→¿hub? card≤5 | 1–4 | sí | **pendiente** |
| `hub_placement_search_medium` | n gaps sum ≤ 20 enum | 4–16 | sí | **pendiente** |
| `route_fa_interval_path_7_10` | intervalos RI path 7–10 nodos | 2–8 | sí | **pendiente** |
| `route_fa_interval_fork_7_10` | intervalos RI fork 7–10 | 2–8 | sí | **pendiente** |
| `route_fa_bag_card_search` | buscar bags card≤4 con RI | 4–24 | no | exploratorio |
| `c8_fin_preconnected_reverify` | re-decide 10 edges fin | 0.1 | sí | hecho en Lean |
| `extended_smoke_fin_decide` | native_decide batches nuevos smokes | 1–4 | sí | **pendiente** |

---

## E. Asintótico / familias (contexto G1, no tw two-chord directo)

| ID | Descripción | CPU h | Paralelo | Estado |
|----|-------------|------:|----------|--------|
| `asymptotic_cubic_n6_n40` | cubic Hamiltonian + chord | 0.5–2 | sí | **pendiente** |
| `asymptotic_cubic_n6_n80` | extensión | 2–8 | sí | exploratorio |

---

## F. Certificados / emisión Lean (CPU moderada)

| ID | Descripción | CPU h | Paralelo | Estado |
|----|-------------|------:|----------|--------|
| `emit_tree_decomp_smokes` | JSON certs smokes | 0.2–1 | sí | opcional |
| `verify_chordwidth_axioms_grep` | auditoría rápida | 0.05 | sí | rutina |

---

## G. Backend proof_complexity (solo si amplías scope fuera ChordWidth)

| Área | Ejemplos | CPU h | Nota |
|------|----------|------:|------|
| outerplanar mass | `outerplanar_*_mass*.py` | 4–40 | otro track |
| multihop / K4 | `multihop_*_mass.py` | 4–40 | otro track |
| xor / bicyclic | `bicyclic_*_mass.py` | 4–40 | otro track |

**No incluidos en manifest default** — activar en `jobs.manifest.json` si necesitas.

---

## Orden recomendado (mínimo tiempo calendario)

1. `lean_cache_get` → `lean_build_chordwidth`
2. En paralelo (4 workers): `tw_exact_n15_n18`, `tw_exact_n19_n24`, `hub_placement_search_small`, `cx_n5_n20`
3. `tw_exact_n25_n32`, `route_fa_interval_path_7_10`, `route_fa_interval_fork_7_10`
4. Exploratorio: push exact boundary, n≥25 exact

**Total CPU h pendiente (ChordWidth focus):** ~40–120 h-núcleo → **10–30 h reloj** con 4 cores.

---

## Perfil high-RAM (≥32 GB)

En notebook con RAM amplia: `bash portable_cpu/bin/run_all.sh --profile high_ram`

- `PORTABLE_CPU_JOBS=6` (o `nproc−1` si mayor)
- TW: sin `--memory-safe`, `--exact-max-nodes 18` (`tw_exact_n15_n24_push_exact18`, `tw_exact_n19_n24_highram`)
- Lean: `LEAN_THREADS=0` (todos los cores)
- Ver `portable_cpu/profiles/high_ram.env` y README § Perfil high-RAM
