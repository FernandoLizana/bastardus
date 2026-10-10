# Frontier dossier: resolution width vs Δ (path toward lower bounds — not P≠NP)

**Evidence:** E2 (certified saturation computations) + constructive E2/E4 lemmas for trees/cycles  
**Claim type:** observation / restricted-theory (Category C)  
**Camino A/B:** **blocked** for P vs NP (see claim-gate demo)

## Intent of this sprint

We are **not** claiming a resolution of P vs NP. We are pushing the laboratory’s strongest *adjacent* research line:

1. Exact / constructive laws for **resolution width** of Tseitin formulas.
2. The **boundary** where `Width(T(G,c)) = Δ(G)` fails.
3. Explicit documentation that this route **fails** the Category-E claim gate for Camino B.

## Settled so far (prior + mass native)

| Statement | Status | Evidence |
|-----------|--------|----------|
| Trees, odd charge ⇒ Width = Δ | Constructive certificates | Python + Rust induction proofs; mass orbits |
| Cycles, odd charge ⇒ Width = 2 = Δ | Constructive saturation | Python + Rust |
| **Unicyclic, odd charge ⇒ Width = Δ** | **Constructive peel+cycle** | `TD-TSEITIN-WIDTH-UNICYCLIC-001`; 378 exhaustive + 708 Rust constructive |
| **Bicyclic Δ≤3, odd charge ⇒ Width = Δ?** | **E2 constructive certs + E3 mass** | peel+Δ-sat certificates; 31k unit + 20k all-odd; 0 W>Δ |
| **Tricyclic can have Width > Δ** | **E2 certified** | n=5, Δ=3, W=4; 720/720 unit |
| “Width = Δ for all G” | **Refuted** | C2 3-regular + tricyclic witnesses |

## Frontier campaign (this sprint)

Native profile `--profile frontier` results (latest):

| Family | Checked | W>Δ | W=Δ | Notes |
|--------|---------|-----|-----|-------|
| Unicyclic n≤6 Δ≤3 | ~10k | 0 | all | Width oracle |
| Constructive unicyclic n=4..5 | 708 | — | — | peel+cycle certs, 0 fails |
| Diamonds / cycle+pendant | 59 | 0 | all | |
| **Bicyclic n=5..6 Δ≤3 unit** | **31050** | **0** | **31050** | No W>Δ |
| **Bicyclic all-odd n=4..5** | **20544** | **0** | **20544** | Strengthens bicyclic conjecture |
| **Tricyclic n=5 Δ≤3 unit** | **720** | **720** | **0** | **All** exceed Δ; first W=4 |

Output: `reports/discovery/mass_verify_frontier_latest.json` / classify reports

**GPU OpenCL (RTX 3050):** `reports/discovery/gpu_width_opencl_classify.json` — bicyclic 600× W=Δ, tricyclic 400× W>Δ; no CPU refine (`MAX_C=1536`).

**Working claims**

1. Unicyclic ⇒ Width=Δ — constructive (dossier UNICYCLIC-001), E4.  
2. **Bicyclic + Δ≤3 ⇒ Width=Δ** — `C-BICYCLIC-WIDTH-EQ-DELTA`; constructive peel+Δ-sat certs (`TD-TSEITIN-WIDTH-BICYCLIC-001`) + 31k unit + **20544 all-odd** (still open as full inductive lemma).  
3. **Tricyclic (γ=3) can have Width>Δ** at n=5, Δ=3: **720/720** dense unit; witness `C_tricyclic_width_gt_delta.json` (W=4).  
4. **Tricyclic can also have Width=Δ** — first witness C₆+{0–2,3–5}, W=Δ=3.  
5. **Law (E2):** on `C_n`+2 chords with Δ≤3: **crossing ⇔ W>Δ**, **non-crossing ⇔ W=Δ** — unit 783/783 (n≤10) + **all-odd 17872/17872** (n≤8). Certificates: upper for non-crossing, lower for crossing. Pendants: apply to the **2-core**; if a pendant raises Δ above the core, W>Δ_full may fail even when the core crosses. See `TD-TSEITIN-WIDTH-CYCLE-TWO-CHORDS-001`.

**Boundary by cyclomatic number γ (|E|−|V|+1 for connected G):**

| γ | Family | Width=Δ (Δ≤3, odd c) |
|---|--------|----------------------|
| 0 | trees | = (proved) |
| 1 | unicyclic | = (constructive) |
| 2 | bicyclic | = (constructive certs + massive checks; inductive lemma open) |
| ≥3 | tricyclic+ | **mixed**: can be > *and* = (both certified) |

**Compact γ/Δ map refresh** (`gamma_delta_width_map.json`: n=5..6 k≤4 Δ≤4; n=7 k≤3 Δ≤3; n=8 k≤2 Δ≤3):
**475** samples. γ≤2 all `eq`; γ≥3 mixed at Δ=3. **Audit:** 49 former `inc` all resolve at **Width = Δ+2** (`gamma_delta_inc_audit.json`); classifier now probes Δ+2.

## Why this cannot become Camino B (P≠NP)

Per `docs/P_VS_NP_CLAIM_GATE.md` and `backend/claim_gate`:

1. **Restricted model:** resolution ≠ general Turing machines / general Boolean circuits.
2. Path-B requirement “covers algorithms not yet invented” **fails** for resolution-only hardness.
3. Barriers `restricted_model` / relativization / natural proofs are not cleared by width oracles.
4. Evidence remains ≤ E2 for computational width; E5/E6 absent.

Demo artifact (gate deliberately fails):

`reports/discovery/claim_gate_camino_b_resolution_blocked.json`

## What would be a legitimate next Lemma (still not P≠NP)

**Next targets (Category C/D):**

1. Lift bicyclic peel+Δ-sat to inductive proof — **advanced:** `prove_bicyclic_pathfold_lemma` (path-fold + ears + width-2; 77/77). See `PROOF_PATHFOLD.md`.  
2. ~~Fine structural law for Cₙ+2 chords~~ **Done (E2).**  
3. Crossing lower bound — path-fold (462/462) + projection 461/461 + **multihop tip-by-tip 461/461** (n=5..10). Lean packs: OneFold / MultiFold / **LongArc**. Family Lean E5 still open.  
4. Noncrossing / outerplanar upper bounds — pathfold certs; outerplanar termination sketch in `TERMINATION.md`.  
5. Triangle-ear XOR: **bare triangle ⇒ □ pure XOR**; length-2 ears with stubs use
   XOR-sum + residual target-sat (**39/39**, `xor_ear_modes.json` / `XOR_EAR.md`).  
7. Lean: `ConcreteClosures` + **`TipElimination`** (non-identity tip projection /
   elimination chain) + `Outerplanar` scaffold. E5 = real Tseitin preserves +
   ear-existence.
8. Noncrossing pathfold mass: **147/147** (n≤9). Bicyclic pathfold: **77/77** (n≤9).
9. XOR both-stubs: obstruction + local-gaussian `gap_remains`; hybrid clips OK.
10. Lean **K4Width3**: Closure₃ pack (16 axioms, no □) + self-projection.
11. Lean **OneFoldProjection**: C₅+(0,2),(1,3) → residual K₄ (`ofoldProjection`).
12. Lean **MultiFoldProjection**: C₆+(0,3),(2,5) → 68→42→16 (`mfEliminationChain`).
13. Lean **LongArcProjection**: C₆+(0,2),(1,3) arc len 2 → 92→42→16 (`laEliminationChain`).
14. Multihop mass: `reports/discovery/multihop_projection_mass.json` — **461/461**.
15. Lean **composeElimination** / `composeProjection` / `composeProjection_trans` / **`composeProjection6`**.
16. Outerplanar: `classify_coherent`, C₄ residual (`earLaw` axiomatized).
17. Lean **TripleFoldProjection**: C₇+(0,4),(1,5) → 118→68→42→16 via LinkedChain + `composeProjection_trans`.
18. Lean **Bicyclic** scaffold (`chordFoldLaw` axiomatized; cites PROOF_PATHFOLD).
19. Lean **FourFoldProjection**: C₈+(0,4),(1,5) → 168→118→92→42→16 via `composeProjection4`.
20. Lean **BicyclicWidth3**: C₄+chord Closure₃ (131) **has □** — Width ≤ Δ.
21. Lean **FiveFoldProjection**: C₉+(0,5),(1,6) → 248→…→16 via LinkedChain + `composeProjection_trans`.
22. Lean **BicyclicC5Width3**: C₅+chord Closure₃ (233) **has □**.
23. Mass full Closure_Δ∋□: bicyclic **48/48**; outerplanar noncrossing **322/322** n≤10 + **33/33** n=11 selective.
24. Ear-existence mass: **701/701** outerplanar Δ≤3 cores n≤14 (`outerplanar_ear_existence_mass_n14.json`).
25. Lean **ThetaChordFold**: `ThetaResidue.chordFoldLaw` — tip exists for every θ-residue.
26. Multihop chains export: **461/461** (`multihop_chains_full.json`); max_tips=6.
27. Lean **`composeProjection_trans`** + **`composeProjection6`** (`ResolutionClosure.lean`).
28. Doc **FAMILY_PROJECTION_E5.md** — esquema inductivo E5.
29. Doc **EAR_LAW_OUTLINE.md** — earLaw + terminación.
30. Barrier fichas: `BARRIER_RELATIVIZATION`, `BARRIER_NATURAL_PROOFS`, `BARRIER_ALGEBRIZATION`, `WHY_WIDTH_IS_NOT_P_NE_NP`.
31. Lean **SixFoldProjection**: C₁₀+(0,2),(1,3) → 652→…→16 via `composeProjection6`.
32. Lean **`StepLink` / `LinkedChain` / `projectionOfLinkedTwo`** (`ResolutionClosure.lean`).
33. Doc **EAR_LAW_TO_ELIMINATION.md** + Lean `FoldTipWitness`.
35. MultiFold via **`projectionOfLinkedTwo`** / `LinkedChain`.
36. Lean **OuterplanarFoldBridge**: `FoldTipWitness` + BicyclicWidth3 empty.
37. γ/Δ `inc` audit: `gamma_delta_inc_audit.json` (reprobe Width ≤ Δ+3).
38. TripleFold via **LinkedChain** + `composeProjection_trans`.
39. XOR gap mass: **45/45** `gap_remains` (`xor_gaussian_gap_mass.json`); `XOR_GAP_STATUS.md`.
40. Ear-existence mass refresh: **701/701** n≤14.
41. FourFold via **LinkedChain** + nested `composeProjection_trans`.
42. Lean Whitney tip lemmas: `tipExists_of_not_cycle`, `tip_or_cycle_of_earLaw`.
43. Bicyclic full Closure_Δ denser (n≤12 + cycle+triangle ear).
44. FiveFold via **LinkedChain** + nested `composeProjection_trans`.
45. Lean **BicyclicC6Width3** (C₆+chord); C₁₂ deferred (`SCALE_LEAN_VS_MASS.md`).
46. Outerplanar Closure_Δ denser n≤10.
47. SixFold via **LinkedChain** + nested `composeProjection_trans`.
48. Outerplanar n=11 selective span-2 ears Closure_Δ.
49. Bicyclic induction plan + Lean `induction_shape_bundle`.
50. Lean **ThetaFoldBridge**: C₆ tip + `bi6_has_empty` bundle.
51. `E5_GAPS_CHECKLIST.md` — gaps G1–G8 for crossing law.
52. Bicyclic pathfold mass denser n≤12.
53. C₆ foldstep diagnostic: ProjectionInclusion fails for pathfold upper-bound
    (`bicyclic_c6_foldstep_projection_check.json`); use constructive pathfold for Width≤Δ.
54. Outerplanar G1: `foldTipWitness_of_not_cycle`, `classify_prefers_triangle`, dichotomy.
55. `SHORT_ARC_TIP_LAW.md` — crossing tip law beyond θ.

See `papers/REMAINING_CHECKLIST.md`.


**Promotion path:** mass frontier → minimal counterexamples → constructive proof → Lean (E5) — still not P≠NP.

## Honest distance to P vs NP

| Milestone | Distance |
|-----------|----------|
| Exact Width law on trees/cycles | Done (local) |
| Full characterization for general graphs | Open (lit. gap) |
| Lift resolution LB → general circuits | **Barrier wall** |
| Camino A or B claim-gate pass | Not approached |

Proximity to a Clay-valid P≠NP proof via this line: **≈ 0**.

See task map: `papers/ROADMAP_P_VS_NP.md`.

## How to re-run

```powershell
$env:Path = "$env:USERPROFILE\.cargo\bin;" + $env:Path
$env:CARGO_TARGET_DIR = "$env:LOCALAPPDATA\tseitin_mass_target"
cd native\tseitin_mass
cargo build --release
& "$env:CARGO_TARGET_DIR\release\tseitin_mass.exe" --profile frontier --out-dir ..\..\reports\discovery
python -m backend.proof_complexity.demo_camino_b_blocked
```
