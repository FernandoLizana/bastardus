# Chord Diagram Tseitin Width — Paper Skeleton

**Status:** Fase 1–2 outline + partial content; Fase 3–5 TBD  
**Audit:** [CROSSING_LAW_SOUNDNESS_AUDIT.md](../reports/CROSSING_LAW_SOUNDNESS_AUDIT.md)  
**Lean:** `lean/PNPLab/ChordWidth/` (build: `lake build PNPLab.ChordWidth.Main`)

---

## 1. Introduction

We study resolution width of Tseitin formulas on **C_n + two chords** with four distinct endpoints and maximum degree Δ = 3. The classical **crossing law** (PNPLab empirical track) states:

- **Noncrossing** chord pairings ⇒ Width = 3 = Δ  
- **Crossing** chord pairings ⇒ Width = 4 > Δ  

Prior PNPLab evidence used finite mass windows, 461-instance catalogs, and ~10k `native_decide` checks ([audit §2–4](../reports/CROSSING_LAW_SOUNDNESS_AUDIT.md)). This paper pivots to a **universal graph-theoretic route**:

\[
\mathrm{Width}(T(G,\varphi)) = \max\bigl(\Delta(G),\,\mathrm{tw}(L(G))\bigr)
\]

where \(L(G)\) is the **line graph** and \(\varphi\) is an **odd marking**. The equality is treated as a **literature hypothesis** (Ben-Sasson–Wigderson; de Colnet–Mengel JAIR 2021; Itsykson et al. SAT 2022), not an original PNPLab theorem.

---

## 2. Background: Tseitin formulas and resolution width

### 2.1 Tseitin encoding

- One Boolean variable per edge of \(G\).  
- At each vertex \(v\), XOR parity of incident edge variables equals charge \(\varphi(v) \bmod 2\).  
- PNPLab encoding: `PNPLab.XorCnf.xorCnfNorm`, parametric instance `CrossingEndpoints.tseitinAxioms`.

### 2.2 Resolution width

Minimum width \(w\) such that the empty clause is derivable by resolution with all intermediate clauses of width ≤ \(w\). PNPLab scaffold: `Derivation`, `derWidth`, `ResolutionWidth` (`PNPLab.ChordWidth.LiteratureHypothesis`).

**Gap (audit §1.1):** PNPLab historically used `WidthClosure` from saturated lists, not global minimum refutation width.

---

## 3. Literature characterization (hypothesis)

**Hypothesis (not proved here):** For every connected \(G\) and odd marking \(\varphi\),

\[
\mathrm{Width}(T(G,\varphi)) = \max\bigl(\Delta(G),\,\mathrm{tw}(L(G))\bigr).
\]

**Primary source (width):** Galesi–Talebanfard–Torán, *TOCT* 2020 (ECCC TR18-170, Corollaries 8 & 16):

> \(w(T(G,c)) = \max\{\mathrm{tw}(L(G)),\ \Delta(G)\}\) for unsatisfiable Tseitin \(T(G,c)\).

The three papers named in the project brief support **size** and **treewidth-parameter** results; they do **not** state the width identity above.

| Reference | Parameter | Exact result (abbrev.) |
|-----------|-----------|--------------------------|
| **Galesi–Talebanfard–Torán (2020)** | **Width** | \(w(T) = \max(\Delta, \mathrm{tw}(L(G)))\) — **hypothesis source** |
| Ben-Sasson & Wigderson (2001) | Width ↔ size | Cor. 3.6: \(S \ge \exp(\Omega((w_\vdash - w_0)^2/n))\); Thm 4.4: \(w \ge e(G)\) (expansion) |
| de Colnet & Mengel, JAIR 2021 | **Regular resolution size** | Thm 1.1: \(S_R \ge 2^{\Omega(\mathrm{tw}(G)/\Delta)}/|V|\); poly refutations iff \(\mathrm{tw}(G)=O(\log n)\) |
| Itsykson–Riazanov–Smirnov, SAT 2022 | **Size (tight)** | \(S_R, S_{\mathrm{OBDD}} \ge 2^{\Omega(\mathrm{tw}(G))}\); upper \(2^{O(\mathrm{tw}(L(G)))}\) for regular resolution |
| Harvey–Wood (2019) | Line-graph tw | Bounds \(\mathrm{tw}(L(G))\) in terms of \(\Delta(G)\), \(\mathrm{tw}(G)\) |

**Line graph vs primal treewidth:** Size lower bounds use \(\mathrm{tw}(G)\); width uses \(\mathrm{tw}(L(G))\). For constant Δ, \(\mathrm{tw}(L(G)) = \Theta(\mathrm{tw}(G))\) up to constants (Prop. in Itsykson et al.).

**Cycle + two chords:** No paper in this list treats \(C_n\) + two chords explicitly. The crossing law (Width 3 vs 4) is an **application** of Galesi width + PNPLab graph bounds on \(\mathrm{tw}(L(G))\) (§4–8).

**Lean:** `TseitinWidthTreewidthCharacterization` — structure field, **LITERATURE HYPOTHESIS** (Galesi et al.).

**Full audit:** [LITERATURE_TSEITIN_WIDTH.md](../reports/LITERATURE_TSEITIN_WIDTH.md). See also [LITERATURE_WIDTH_VS_DELTA.md](LITERATURE_WIDTH_VS_DELTA.md).

---

## 4. Cycle + two chords

Four sorted endpoints \(p_0 < p_1 < p_2 < p_3 < n\) on \(C_n\). Three pairings:

| Pairing | Chords | Geometry |
|---------|--------|----------|
| Crossing | \(\{p_0,p_2\}, \{p_1,p_3\}\) | Cross inside disk |
| Nested | \(\{p_0,p_3\}, \{p_1,p_2\}\) | One chord inside other |
| Disjoint | \(\{p_0,p_1\}, \{p_2,p_3\}\) | Parallel bundles |

**Lean:** `CycleTwoChordGraph`, `chordsCross`, bridge to `CrossingEndpoints.toSimpleGraph`.

**Smoke:** `c5OfoldGraph` (crossing), `c8NestedGraph` (noncrossing).

---

## 5. Line graph and treewidth

### 5.1 Line graph \(L(G)\)

Vertices = edges of \(G\); adjacency = share a vertex. **Mathlib v4.32.0:** `SimpleGraph.lineGraph` — imported in `PNPLab.ChordWidth.LineGraph`.

### 5.2 Treewidth

Mathlib v4.32.0 has **no** graph treewidth API ([audit §3.6](../reports/CROSSING_LAW_SOUNDNESS_AUDIT.md)). Phase 1 uses `TreewidthWitness` (Prop stub). Phase 3: real tree decomposition or upstream Mathlib import.

**Target values (two-chord Δ = 3):**

| Case | Expected tw(\(L(G)\)) | max(3, tw) |
|------|------------------------|------------|
| Noncrossing | **3** | 3 |
| Crossing (K₄ core) | **4** | 4 |

**Empirical checks:**
- **Representative** (2026-08-02): n=5..100 — **383/383** — [CHORD_TREewidth_VERIFICATION.md](../reports/CHORD_TREewidth_VERIFICATION.md)
- **Exact sweep** (2026-08-03): n=5..14 — **2870/2870** gap configs, 0 counterexamples — [CHORD_TREewidth_EXACT_N5_N14.md](../reports/CHORD_TREewidth_EXACT_N5_N14.md)

Script: `scripts/verify_chord_treewidth.py` (C(n,4) blocked for n>16 unless `--full-endpoints`; exact bitset search in `scripts/treewidth/compute.py`).

## 6. Degree-2 suppression and branch core

Suppress degree-2 vertices on paths between **branch vertices** (degree ≠ 2). Yields `SuppressedCore` with branch set + path-length data.

**Lean:** `PNPLab.ChordWidth.DegreeTwoSuppression` — combinatorial definitions; proofs Phase 3.

---

## 7. Crossing case: K₄ core

### 7.1 Degree-2 suppression narrative

On \(G = C_n\) + two chords with \(\Delta(G) = 3\), most cycle vertices have degree 2: they lie on simple paths between **branch vertices** (degree \(\neq 2\)). In the crossing regime there are exactly **four** branch vertices — the chord endpoints — each of degree 3.

**Degree-2 suppression** (PNPLab combinatorial convention):

1. Identify branch vertices \(B = \{v : \deg(v) \neq 2\}\).
2. Replace each maximal path of degree-2 vertices between \(u, v \in B\) by a single **parallel class** recorded by path length.
3. The **suppressed core** is the graph on \(B\) with adjacency data given by those parallel classes.

Intuition: resolution width and line-graph treewidth depend on the **branch structure**, not on the length of subdivided cycle segments. Longer \(n\) adds degree-2 chains but does not change the core type.

**Lean:** `PNPLab.ChordWidth.DegreeTwoSuppression` — `isBranchVertex`, `branchVertices`, `suppressDegreeTwoPaths`, `canonicalSuppressedCore`; `CycleTwoChordGraph.suppressedCore` wired via `canonicalSuppressedCore`. Transport lemmas along graph equality (`branchVertices_congr`, `branchSuppressAdjacent_of_graph_eq`, …). Path-length parallel classes between branch pairs remain **TODO** for full combinatorial suppression.

**Prior PNPLab track (reused intuition, not ChordWidth proof):** combinatorial fold schedules landing on `K4Skeleton` (`CrossingFoldSchedule`, `K4Width3`, `k4Axioms`) — instance-level width-4 evidence, not a universal tw(\(L(G)\)) theorem.

### 7.2 K₄ vs C₄ classification

| Regime | Chord geometry | Branch set | Suppressed core (target) | tw(\(L(G)\)) target |
|--------|----------------|------------|---------------------------|---------------------|
| **Crossing** | \(\{p_0,p_2\},\{p_1,p_3\}\) cross | 4 endpoints | **\(K_4\)** (six edge classes) | **4** |
| **Noncrossing** | nested or disjoint | 4 endpoints | **\(C_4\)** + parallel bundles | **3** |

When chords cross, the four branch vertices pairwise connect through cycle segments and chord edges; after suppression the abstract core is the complete graph **\(K_4\)**. When chords do not cross, the core is a **4-cycle** \(C_4\) with two pairs of parallel paths (outerplanar ear regime; §8).

**Lean (Phase 3 smoke + instance):** `PNPLab.ChordWidth.TwoChordCore` — structural predicates `SuppressedCore.isK4` (4 branch verts, 6 suppress-edges) and `SuppressedCore.isFourCycle` (4 branch verts, degree 2, 4 edges). Proved on smoke graphs via `native_decide`, transported to instances:

- `c5Ofold_crossing_core_k4` — crossing \(C_5\) (`c5OfoldGraph`).
- `c8Nested_noncrossing_core` — nested \(C_8\) (`c8NestedGraph`).

**Remaining:** `SimpleGraph.Iso` to `completeGraph (Fin 4)` / `cycleGraph 4`; universal ∀n classification.

### 7.3 Line-graph treewidth and Galesi width link

Under the **Galesi–Talebanfard–Torán width hypothesis** (§3),

\[
\mathrm{Width}(T(G,\varphi)) = \max\bigl(3,\, \mathrm{tw}(L(G))\bigr)
\]

for connected \(G\) with \(\Delta = 3\) and odd marking \(\varphi\). The crossing law \(\mathrm{Width} = 4\) therefore reduces to proving \(\mathrm{tw}(L(G)) = 4\) in the crossing case (since \(\max(3,4) = 4\)).

For \(K_4\), \(\mathrm{tw}(K_4) = 3\); the target **4** is treewidth of **\(L(G)\)**, not of the primal suppressed core. The K₄ core argument is expected to force a \(K_4\)-type obstruction in the line graph (or an elimination order of width 4). Nominal stub: `k4TreewidthWitness` in `TwoChordCore.lean` (literature value tw(\(K_4\)) = 3 — used for core, not final L(G) bound).

**Conditional Lean theorem (proved):** if literature holds and tw(\(L(G)\)) = \(k\), then \(\mathrm{Width} = \max(3,k)\) — `width_from_treewidth_of_characterization`, `two_chord_width_from_characterization`.

### 7.4 Python / empirical support

External verification ([CHORD_TREewidth_VERIFICATION.md](../reports/CHORD_TREewidth_VERIFICATION.md)):

- Script: `scripts/verify_chord_treewidth.py`
- Range: \(n = 5..100\), 383 valid \(\Delta = 3\) representative configurations
- Result: **383/383 matches**, 0 counterexamples
- Crossing instances (192): all observed tw(\(L(G)\)) = **4**
- Methods: exact bruteforce elimination for \(|V(L(G))| \le 7\); NetworkX min-fill-in upper bound for larger \(n\) (heuristic — not a proof)

This supports the conjecture tw(\(L(G)\)) = 4 for crossing pairings but **does not replace** a Lean or pen-and-paper proof.

### 7.5 Phase 3 status (honest)

| Item | Status |
|------|--------|
| Branch vertex / `SuppressedCore` / `canonicalSuppressedCore` | **Done** |
| Structural `SuppressedCore.isK4` / smoke `c5Ofold_crossing_core_k4` | **Done** (`native_decide` + transport) |
| `CrossingCoreIsK4` instance witness on `c5OfoldGraph` | **Done** |
| Prove suppressed core \(\cong K_4\) (`SimpleGraph.Iso`) | **TODO** |
| Prove tw(\(L(G)\)) = 4 (crossing, all \(n\)) | **TODO** |
| Replace `TreewidthWitness` with real tw bounds | **TODO** (Mathlib PR [#38334](https://github.com/leanprover-community/mathlib4/pull/38334)) |
| `CrossingLineGraphTw` — tighten to \(k = 4\) | **TODO** |

---

## 8. Noncrossing case: 4-cycle core

### 8.1 Degree-2 suppression narrative

The noncrossing regimes (**nested** and **disjoint** pairings from §4) share the same branch-vertex pattern: four endpoints of degree 3, all other vertices degree 2 on the cycle. Suppression collapses each cycle segment between endpoints to a path-length label.

The resulting **suppressed core** is not a single edge or tree: it is a **4-cycle** \(C_4\) where opposite branches may be connected by **parallel path pairs** (different cycle lengths depending on \(n\) and pairing). Geometry is **outerplanar** — no crossing chords — so classical outerplanar / ear-decomposition arguments apply at the primal level (Whitney ear laws; PNPLab scaffold `NoncrossingTwoChordsEar` in the legacy track).

**Lean:** same `DegreeTwoSuppression` module as §7; `NoncrossingCoreIsFourCycle` in `TwoChordCore.lean` targets the \(C_4\) + parallel-bundle classification. Smoke: `c8Nested_noncrossing_core` on `c8NestedGraph`.

### 8.2 K₄ vs C₄ classification (noncrossing side)

The **dichotomy** for the two-chord family:

\[
\text{chords cross} \;\Longleftrightarrow\; \text{suppressed core is } K_4\text{-type}
\qquad
\text{noncrossing} \;\Longleftrightarrow\; \text{suppressed core is } C_4\text{-type}.
\]

Noncrossing graphs are outerplanar, hence \(\mathrm{tw}(G) \le 2\). For bounded \(\Delta\), Harvey–Wood-type bounds give \(\mathrm{tw}(L(G)) = O(\Delta \cdot \mathrm{tw}(G)) = O(1)\); the **sharp** values needed for Galesi width are tw(\(L(G)\)) = **3** (not 2), matching \(\max(3, \mathrm{tw}(L(G))) = 3 = \Delta\).

| Pairing | Example smoke | Core target | tw(\(L(G)\)) target | Width (via Galesi) |
|---------|---------------|-------------|---------------------|---------------------|
| Nested | `c8NestedGraph` | \(C_4\) + bundles | 3 | 3 |
| Disjoint | (same class) | \(C_4\) + bundles | 3 | 3 |

Nominal stub: `fourCycleTreewidthWitness` — tw(\(C_4\)) = 2 (primal core; line-graph value still Phase 3).

**Conditional Lean theorem (proved):** `noncrossing_width_eq_three_when_tw_le_two` — if literature holds, noncrossing, and tw(\(L(G)\)) \(\le 2\), then width = 3. Phase 3 must upgrade the tw bound from \(\le 2\) to **= 3** on \(L(G)\) for the full crossing law branch.

### 8.3 Python / empirical support

Same run as §7.4 ([CHORD_TREewidth_VERIFICATION.md](../reports/CHORD_TREewidth_VERIFICATION.md)):

- Noncrossing instances (191): all observed tw(\(L(G)\)) = **3**
- Combined with crossing cases: geometry determines tw(\(L(G)\)) in all 383 tested representatives

CSV: `reports/chord_treewidth_verification.csv`. Caveat: heuristic upper bounds for large \(n\); exact only on small line graphs.

### 8.4 Galesi width link

With \(\Delta = 3\) and tw(\(L(G)\)) = 3, the Galesi formula yields \(\mathrm{Width}(T(G,\varphi)) = \max(3,3) = 3\) — the **noncrossing** branch of the crossing law. PNPLab does **not** reprove Galesi; it is imported as `TseitinWidthTreewidthCharacterization` (`LiteratureHypothesis.lean`).

### 8.5 Phase 3 status (honest)

| Item | Status |
|------|--------|
| Structural `SuppressedCore.isFourCycle` / smoke `c8Nested_noncrossing_core` | **Done** (`native_decide` + transport) |
| `NoncrossingCoreIsFourCycle` instance witness on `c8NestedGraph` | **Done** |
| Prove suppressed core \(\cong C_4\) with parallel bundles | **TODO** |
| Prove tw(\(L(G)\)) = 3 (noncrossing, all \(n\)) | **TODO** (Python: 191/191 representatives) |
| Outerplanar / Whitney ear formalization | **TODO** (Mathlib lacks `IsOuterplanar` in v4.32) |
| `NoncrossingLineGraphTw` — align with observed \(k = 3\) on \(L(G)\) | **TODO** |
| Universal \(\forall n\) dichotomy (§9, Phase 5) | **Partial** — conditional per-instance; unconditional ∀n open |

---

## 9. Conditional main theorem (Fase 1–4)

**Proved (conditional on literature + tw witnesses):**

If `TseitinWidthTreewidthCharacterization` holds for \(G\), \(\Delta(G) = 3\), and tw(\(L(G)\)) = \(k\), then  
\(\mathrm{Width}(T(G,\varphi)) = \max(3, k)\) for all odd \(\varphi\).

**Lean:** `width_from_treewidth_of_characterization`, `two_chord_width_from_characterization`.

**Fase 4 corollaries (smoke + hypothesis tw):**

| Case | tw(\(L(G)\)) witness | Width | Lean |
|------|----------------------|-------|------|
| Crossing + K₄ core | 4 | **4** | `crossing_width_eq_four` (`Laws/CrossingWidth4.lean`) |
| Noncrossing + C₄ core | 3 | **3** | `noncrossing_width_eq_three_when_tw_eq_three` (`Laws/NoncrossingWidth3.lean`) |

Smoke: `c5Ofold_crossing_lineGraph_tw4`, `c8Nested_noncrossing_lineGraph_tw3`. tw values are **hypothesis fields** (Python-validated), not proved ∀n.

**Fase 5 conditional dichotomy (per-instance, [Lean Fase 5](d87403f2-034f-412d-95ed-a680569325d9)):**

Given `TwoChordWidthDichotomy` for a fixed `CycleTwoChordGraph` and odd φ: crossing ⇒ Width = 4; noncrossing ⇒ Width = 3.

**Lean:** `two_chord_width_dichotomy_conditional`, `cycle_two_chords_resolution_width_conditional` (`CycleTwoChords/Dichotomy.lean`, `MainTheorem.lean`). Build: 1058 jobs green.

**Dichotomy (Phase 5 unconditional — not yet proved):**

\[
\forall n,\ \forall\text{ two-chord }G,\ \forall\text{ odd }\varphi:\quad
\mathrm{Width} = 3 \leftrightarrow \text{noncrossing}.
\]

---

## 10. Relation to prior PNPLab work

| Prior track | Status in pivot |
|-------------|-----------------|
| `CycleTwoChordsLaw` (1421 / 394768 / 461 mass) | Empirical; not universal ([audit §2](../reports/CROSSING_LAW_SOUNDNESS_AUDIT.md)) |
| `ParametricDischarge*` catalogs | **Not used** in ChordWidth proof |
| `CrossingEndpoints.toSimpleGraph`, `tseitinAxioms` | **Reused** |
| K₄ width-3 closure, projection | **Reused** as lower-bound intuition |
| `native_decide` on 461 instances | **Replaced** by graph-theoretic target |

---

## 11. Roadmap (Fase 3–5)

| Phase | Goal | Status (2026-08-03) | Lean module |
|-------|------|------------------------|-------------|
| **3** | Degree-2 suppression; structural K₄/C₄ smoke; elimination scaffolding | **Done (Lean MVP green)** — iso + real tw deferred | `DegreeTwoSuppression.lean`, `TwoChordCore.lean`, `Treewidth.lean` |
| **4** | tw(\(L(G)\)) = 3/4; Width = 3/4 via Galesi | **Partial (green build)** — conditional Width 3/4 + smoke tw witnesses; tw(L(G)) ∀n and elimination orders **deferred** | `Laws/CrossingWidth4.lean`, `Laws/NoncrossingWidth3.lean` |
| **5** | ∀n dichotomy; Width = 3 ↔ noncrossing | **Partial** — conditional `cycle_two_chords_resolution_width_conditional`; unconditional ∀n open | `CycleTwoChords/Dichotomy.lean`, `MainTheorem.lean` |

### Fase 5 exit (partial — [Lean Fase 5](d87403f2-034f-412d-95ed-a680569325d9))

- `TwoChordWidthDichotomy`, `two_chord_width_dichotomy_conditional`, `cycle_two_chords_resolution_width_conditional`.
- Per-instance only (hypothesis tw + literature per graph); build 1058 jobs green.

### Fase 5 remaining

1. Unconditional `cycle_two_chords_resolution_width` — ∀n ≥ 5, ∀ valid G, ∀ odd φ.
2. Prove tw(L(G)) = 4 / = 3 for all valid instances (replace hypothesis witnesses).
3. ∀n core classification + `SimpleGraph.Iso` to K₄ / C₄.
4. Unified literature char; full odd-marking Tseitin encoding.

### Fase 4 exit (partial — [Lean Fase 4](e366de8a-5dfb-4513-b374-ff37fc98fb1a))

- `CrossingLineGraphTw4` / `NoncrossingLineGraphTw3` hypothesis witnesses on c5/c8 smoke.
- `crossing_width_eq_four`, `noncrossing_width_eq_three_when_tw_eq_three`.
- Build: 1056 jobs green.

### Fase 4 remaining (blockers for unconditional Fase 5)

1. Mathlib `SimpleGraph.treeWidth` (PR [#38334](https://github.com/leanprover-community/mathlib4/pull/38334)).
2. Prove tw(\(L(G)\)) = 4 / = 3 **∀n** (replace hypothesis witnesses).
3. `SimpleGraph.Iso` to K₄ / C₄; line-graph elimination orders on smoke.
4. Full odd-marking Tseitin encoding.

### Fase 4 entry criteria (legacy — partially met)

1. Mathlib `SimpleGraph.treeWidth` (or pathwidth) pinned and imported.
2. `SimpleGraph.Iso` proofs: suppressed core ≅ K₄ (crossing) / ≅ C₄ + bundles (noncrossing).
3. tw(\(L(G)\)) = 4 (crossing) and = 3 (noncrossing) for all valid instances.
4. Instantiate Galesi hypothesis → `CrossingWidth4` / `NoncrossingWidth3`. **Done (conditional + smoke).**

### Fase 5 target

Universal theorem: ∀n ≥ 5, ∀ valid two-chord G, ∀ odd φ — Width(\(T(G,\varphi)\)) = 3 ↔ noncrossing. Full detail: [FASE5_ROADMAP.md](../reports/FASE5_ROADMAP.md).

**Build:** `LEAN_NUM_THREADS=2 lake build PNPLab.ChordWidth.Main` — no `sorry`, no axioms; literature as structure fields.

---

## References (short)

1. Tseitin (1968)  
2. Ben-Sasson & Wigderson (2001) — width↔size; expansion width lower bounds  
3. **Galesi, Talebanfard & Torán (2020)** — **width = max(Δ, tw(L(G)))**  
4. de Colnet & Mengel, JAIR 2021 — regular-resolution size vs tw(G)  
5. Itsykson, Riazanov & Smirnov, SAT 2022 — tight size \(2^{\Omega(\mathrm{tw}(G))}\)  
6. Harvey & Wood (2019) — treewidth of line graphs  
7. Literature audit: [LITERATURE_TSEITIN_WIDTH.md](../reports/LITERATURE_TSEITIN_WIDTH.md)  
8. PNPLab audit: `reports/CROSSING_LAW_SOUNDNESS_AUDIT.md`
