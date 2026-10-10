# Theorem dossier TD-TSEITIN-WIDTH-CYCLE-TWO-CHORDS-001

## Statement (working)

Let `G` be the cycle `C_n` (`n ≥ 4`) plus **two chords** on four **distinct**
endpoints, with `Δ(G) ≤ 3`, and let `c` be an **odd** charge.

| Geometry of the two chords on the cycle | Resolution width |
|-----------------------------------------|------------------|
| **Non-crossing** | `Width(T(G,c)) = Δ(G)` |
| **Crossing** | `Width(T(G,c)) > Δ(G)` |

Crossing means the four endpoints alternate around the cycle
(standard chord-crossing). Under `Δ ≤ 3`, shared endpoints are impossible
(would force degree ≥ 4), so the chords use four distinct vertices.

## Evidence (E2)

| Check | Result | Artifact |
|-------|--------|----------|
| Unit charge, `n = 5..11` | **1421/1421** | `reports/discovery/chord_law_Cn_plus_2.json` |
| All odd charges, `n = 5..13` | **256784/256784** | `reports/discovery/crossing_law_all_odd.json` |
| First `W=Δ` witness | `C_6 + {0–2, 3–5}` | `datasets/examples/tricyclic_width_eq_delta.json` |

## Certificates (machine-checked)

- **Upper (non-crossing, general):** peel + width-Δ saturation —
  `prove_noncrossing_two_chords_lemma`.
- **Upper (non-crossing, both chords length 2):** structured resolution —
  peel → per-ear target derivation → width-2 finish —
  `prove_noncrossing_len2_ears_lemma`
  (`reports/discovery/ear_clip_resolution_len2.json`).
- **Lower (crossing):** complete width-Δ closure has no empty clause —
  `certify_crossing_width_gt_delta` (odd-charge UNSAT ⇒ `Width ≥ Δ+1`).
- **Pendants:** law on the **2-core**; raising Δ with a pendant can break `W>Δ_full`.

## Proof outline (human — not yet Lean)

### A. Structural dichotomy

Drawing `C_n` as a circle:

1. **Non-crossing chords** can be drawn inside the disk without crossings ⇒
   `G` is **outerplanar**.
2. **Crossing chords** cannot ⇒ `G` is **not outerplanar**.

Under `Δ ≤ 3` and exactly two chords on four endpoints, the crossing case always
contains a **`K_4`-minor** (contract the four paths between the endpoints of the
crossing pair). Direct small case: `C_4` with both diagonals is exactly `K_4`,
and for that graph one has `Width = 4 > Δ = 3` (certified).

### B. Upper bound (non-crossing) — intended induction

Goal: prove `Width ≤ Δ` for odd-charge Tseitin on this outerplanar family
(ideally: all outerplanar `Δ ≤ 3`).

**Geometric fact (machine-checked on the family):** crossing ⇔ not outerplanar
(`n = 5..10`, 783 graphs, 0 mismatches).

**Plan (induction on `n + #chords`):**

1. Peel degree-1 vertices by the Unit–XOR lemma (tree induction) — width ≤ Δ.
2. On a 2-core that is `C_k` + two **non-crossing** chords:
   - **Length-2 ear case:** each length-2 chord gives a facial triangle with a
     degree-2 tip. Clip tips (absorb charge) → residual **cycle**.
     GF(2) check: **65/65** (`ear_clip_noncrossing_len2.json`).
     Resolution derivation: `prove_noncrossing_len2_ears_lemma`
     (`ear_clip_resolution_len2.json`).
   - Longer / nested chords: clip shortest ears first; residual goes to
     unicyclic/bicyclic lemmas (still partly saturation-based).

**Status:** Length-2 double-ear case has a verified resolution certificate
organized by ears; general non-crossing still uses peel+Δ-sat; hand XOR-rewrite
without search remains open.

### C. Lower bound (crossing) — intended invariant

Goal: show width-Δ saturation never produces `⊥`.

**Plan:**

1. Crossing ⇒ `K_4`-minor with odd effective charge on a 4-vertex core
   (after contracting paths / peeling). **Ingredient certified:** every crossing
   `C_n`+2 chords instance with Δ≤3 has a K₄-minor model (`n=5..12`, 1286/1286 —
   `reports/discovery/k4_minor_crossing_law.json`).
2. Direct computation on `K_4`: width-3 closure has no `⊥`; width-4 admits `⊥`
   (same report: Width=4>Δ=3).
3. Lift: a width-Δ derivation on `G` would restrict / project to a width-Δ
   derivation on the `K_4` minor — **analytic gap.**  
   Charge-contraction ingredients checked on **461** crossing instances
   (`k4_lift_charge_contraction.json`). See `LIFT_K4.md`.

**Status:** Ingredients + charge-contraction agreement on the crossing family
(`k4_lift_charge_contraction.json`, 461/461 in the n≤10 unit sweep). See
`LIFT_K4.md`. Projection lemma for resolution width still open.

### D. What this is not

Resolution-only. **Camino A/B (P vs NP) remains blocked.** No Clay claim.

## Code

- Geometry: `backend/proof_complexity/chord_crossing_law.py`
- Certificates: `backend/proof_complexity/constructive_proofs.py`
  (`prove_noncrossing_two_chords_lemma`, `certify_crossing_width_gt_delta`)
- Search / verify: `chord_law_search.py`, `verify_crossing_all_odd.py`
