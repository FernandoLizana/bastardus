# Community question drafts — ChordWidth / line-graph treewidth

**Project:** PNPLab ChordWidth pivot ([CHORD_DIAGRAM_TSEITIN_WIDTH.md](../papers/CHORD_DIAGRAM_TSEITIN_WIDTH.md))  
**Status:** Fase 1–3 Lean MVP green (structural K₄/C₄ smoke); **Fase 4 blocked on Mathlib treewidth API** + real tw(L(G)) bounds  
**Generated:** 2026-08-03

---

## 1. Lean Zulip (#mathlib4 or #new members)

### Context (paste first)

We are formalizing a graph-theoretic route to the PNPLab **crossing law** for Tseitin resolution width on **C_n + two chords** (four distinct endpoints, Δ = 3). The intended pipeline is:

1. **Literature hypothesis** (Galesi–Talebanfard–Torán, TOCT 2020):  
   \(w(T(G,\varphi)) = \max(\Delta(G),\, \mathrm{tw}(L(G)))\) for unsatisfiable Tseitin on connected \(G\).
2. **Graph side:** classify the suppressed branch core after degree-2 suppression — **K₄** when chords cross, **C₄** when noncrossing — and bound \(\mathrm{tw}(L(G))\) accordingly (target: 4 vs 3).
3. **Lean (Phase 3 done):** `PNPLab.ChordWidth` has conditional theorems (`width_from_treewidth_of_characterization`), degree-2 suppression, and **structural K₄/C₄ smoke proofs** (`c5Ofold_crossing_core_k4`, `c8Nested_noncrossing_core`) — but **no real treewidth API** yet; we use `TreewidthWitness` stubs. **Phase 4** needs Mathlib tw bounds on \(L(G)\), not just core classification.
4. **Python (computational evidence, not proof):** exact sweep **2870/2870** for n = 5..14; representative sweep **383/383** for n = 5..100 — see §Evidence below.

Mathlib pin: **v4.32.0** — `SimpleGraph.lineGraph` is available; treewidth is not.

---

### Question A — Mathlib treewidth / TreeDecomp (blocking Phase 4)

> **We need real `SimpleGraph.treeWidth` (or pathwidth) in Mathlib to prove tw(L(G)) ∈ {3,4} for cycle + two chords. Does v4.32+ already have this, and what is the status of PR [#38334](https://github.com/leanprover-community/mathlib4/pull/38334)? Should we upgrade our pin or keep local elimination witnesses until it lands?**

**What we've verified:**
- v4.32.0 has `SimpleGraph.lineGraph` (`Mathlib.Combinatorics.SimpleGraph.LineGraph`) — imported in `PNPLab.ChordWidth.LineGraph`.
- Audit ([LITERATURE_TSEITIN_WIDTH.md](LITERATURE_TSEITIN_WIDTH.md) §7): no `TreeDecomp`, `SimpleGraph.treeWidth`, or `IsOuterplanar` in the v4.32 pin.
- PR #38334 (Apr 2026, assigned YaelDillies) appears open / in review; follow-up #39939 depends on it.
- Phase 3 Lean MVP is **green** (1054 jobs, no `sorry`) — but tw bounds on **L(G)** are still stubs, not Mathlib lemmas.

**What we need (Phase 4 gate):**
- Whether upgrading past v4.32.0 is worthwhile **now**, or we should keep `EliminationOrder` witnesses locally until #38334 merges.
- Pointers to **already-merged** treewidth lemmas we missed: tw(K₄), tw(C₄), line-graph bounds, separator lemmas.
- Review guidance: pathwidth-first design (#38334 review notes) — should ChordWidth target pathwidth initially?

---

### Question B — Proving tw(L(G)) = 3 vs 4 from K₄/C₄ core structure

> **For G = C_n + two chords (Δ = 3), after degree-2 suppression the branch core is K₄ (crossing) or C₄ + parallel bundles (noncrossing) — we have Lean smoke proofs for this on c5Ofold / c8Nested. What is the recommended Mathlib approach to lift this to tw(L(G)) ∈ {3,4}? Direct elimination on L(G), or primal tw(G) + Harvey–Wood line-graph inequalities?**

**What we've verified:**
- **Exact Python** (2026-08-03): n = 5..14, gap-pattern sweep — **2870/2870** exact tw(L(G)), 0 counterexamples ([CHORD_TREewidth_EXACT_N5_N14.md](CHORD_TREewidth_EXACT_N5_N14.md)). Noncrossing: 1870 configs, all tw = 3. Crossing: 1000 configs, all tw = 4.
- **Representative Python** (2026-08-02): n = 5..100 — **383/383** witnesses match dichotomy ([CHORD_TREewidth_VERIFICATION.md](CHORD_TREewidth_VERIFICATION.md)). Noncrossing: 191 at tw = 3; crossing: 192 at tw = 4. (Larger n uses NetworkX min-fill-in **upper bound** — heuristic, not proof.)
- **Lean smoke:** `c5Ofold_crossing_core_k4`, `c8Nested_noncrossing_core` in `TwoChordCore.lean` — structural `SuppressedCore.isK4` / `isFourCycle` via `native_decide` + graph transport. **Not** `SimpleGraph.Iso` to `completeGraph (Fin 4)` / `cycleGraph 4`.
- Combinatorial scaffold: `DegreeTwoSuppression.lean` (`branchVertices`, `canonicalSuppressedCore`); classification structures `CrossingCoreIsK4` / `NoncrossingCoreIsFourCycle`.

**What we need:**
- Proof strategy for tw(L(G)) = 4 from K₄-type core (crossing) and tw(L(G)) = 3 from C₄-type core (noncrossing) — ideally ∀n, not just smoke instances.
- Examples of similar “suppress degree-2 → classify core → bound tw” proofs in Mathlib or downstream projects.
- Whether outerplanarity (`IsOuterplanar`) is the right lever for the noncrossing branch, and if so, what exists upstream.

---

### Question C — Collaboration / Tseitin width ↔ line-graph treewidth

> **Is anyone formalizing Galesi et al. (TOCT 2020) width = max(Δ, tw(L(G))) or working on line-graph treewidth for bounded-degree graph families?** We are pivoting PNPLab's crossing law (Tseitin width 3 vs 4 on cycle + two chords) to this route. Phase 3 Lean scaffold + 2870 exact / 383 representative Python checks are ready to share — happy to link audit reports and CSV if useful.

**Links (if attachments allowed):**
- Paper skeleton: `papers/CHORD_DIAGRAM_TSEITIN_WIDTH.md`
- Literature audit: `reports/LITERATURE_TSEITIN_WIDTH.md`
- Lean status: `reports/CHORD_WIDTH_LEAN_STATUS.md`
- Exact validation: `reports/CHORD_TREewidth_EXACT_N5_N14.md`
- Roadmap (Fase 4–5): `reports/FASE5_ROADMAP.md`

---

## 2. MathOverflow (optional)

**Title:** Does chord crossing exactly determine tw(L(G)) ∈ {3,4} for C_n + two chords (Δ = 3)? — 2870 exact checks for n ≤ 14

### Context

Let \(G\) be an \(n\)-cycle \(C_n\) with two additional edges (chords) between **four distinct** vertices, so \(\Delta(G) = 3\). There are three endpoint pairings (crossing, nested, disjoint); **crossing** means the chords intersect in the planar embedding of the cycle.

We study **treewidth of the line graph** \(L(G)\) (vertices = edges of \(G\); adjacency = share a vertex). This arises from the resolution-width characterization for Tseitin formulas (Galesi–Talebanfard–Torán, *TOCT* 2020, ECCC TR18-170):

\[
w(T(G,c)) = \max\bigl\{\Delta(G),\, \mathrm{tw}(L(G))\bigr\}
\]

for unsatisfiable Tseitin \(T(G,c)\) on connected \(G\). With \(\Delta = 3\), the PNPLab **crossing law** predicts resolution width **3** for noncrossing pairings and **4** for crossing pairings — equivalently, we conjecture:

| Geometry   | \(\mathrm{tw}(L(G))\) | \(\max(3, \mathrm{tw}(L(G)))\) |
|------------|------------------------|---------------------------------|
| Noncrossing | **3**                 | 3                               |
| Crossing    | **4**                 | 4                               |

After **degree-2 suppression** (contract paths between branch vertices of degree ≠ 2), the branch core is expected to be **K₄** (crossing) or **C₄ with parallel bundles** (noncrossing). We have Lean smoke proofs of the structural core classification on small instances; we do **not** yet have graph isomorphism or universal tw bounds.

---

### Precise question

**For all \(n \ge 5\) and all valid two-chord instances on \(C_n\) with four distinct endpoints and \(\Delta(G) = 3\), is it true that**

\[
\mathrm{tw}(L(G)) = \begin{cases} 3 & \text{if the chords do not cross}, \\ 4 & \text{if the chords cross?} \end{cases}
\]

Equivalently: does the crossing bit of the chord diagram **exactly** determine \(\mathrm{tw}(L(G))\) in this family?

We are **not** asking for the full Galesi width theorem — only the line-graph treewidth dichotomy for this graph family.

---

### What we've verified (computational evidence — not a proof)

| Sweep | Range | Method | Result |
|-------|-------|--------|--------|
| **Exact** | n = 5..14 | Gap-pattern enumeration, exact tw search (2814/2870 via width search; 56 bruteforce) | **2870/2870** match, **0 counterexamples** |
| **Representative** | n = 5..100 | Rotation-normalized witnesses per n | **383/383** match, **0 counterexamples** |

Breakdown (exact sweep, n ≤ 14):
- Noncrossing: **1870** configurations, all \(\mathrm{tw}(L(G)) = 3\).
- Crossing: **1000** configurations, all \(\mathrm{tw}(L(G)) = 4\).

Breakdown (representative sweep, n ≤ 100):
- Noncrossing: **191** witnesses, all tw = 3.
- Crossing: **192** witnesses, all tw = 4.

**Caveats:**
- Exact sweep covers all Δ = 3 gap-pattern configs for n ≤ 14 only.
- Representative sweep for n ≥ 7 uses NetworkX min-fill-in as an **upper bound** (validated against exact C₅/C₆ witnesses) — strong evidence but not a proof for all n.
- Script: `scripts/verify_chord_treewidth.py`; reports: [CHORD_TREewidth_EXACT_N5_N14.md](CHORD_TREewidth_EXACT_N5_N14.md), [CHORD_TREewidth_VERIFICATION.md](CHORD_TREewidth_VERIFICATION.md).

**Literature:** Galesi et al. give the width formula; Harvey–Wood and line-graph literature give generic tw(L(G)) vs tw(G) bounds for bounded Δ, but **no paper in our review** treats cycle + two chords explicitly ([LITERATURE_TSEITIN_WIDTH.md](LITERATURE_TSEITIN_WIDTH.md) §6).

**Formalization (in progress):** Lean 4 scaffold with structural K₄/C₄ smoke instances — no graph isomorphism or tw(L(G)) theorem yet.

---

### What we need from the community

1. **Proof or counterexample** for the tw(L(G)) dichotomy — even a fixed-n argument with a generalization template would help.
2. **Known results** on line-graph treewidth for outerplanar vs crossing chord graphs, or for “cycle + k chords” families.
3. **Sharper characterization** — e.g. is tw(L(G)) = 3 iff G is outerplanar in this Δ = 3 regime? (Noncrossing cases are outerplanar; crossing cases admit a K₄ branch core after suppression.)
4. Pointers if this is folklore or appears in cop–robber / resolution-width papers beyond Galesi et al.

---

### Tags (suggested)

`graph-theory` `treewidth` `line-graph` `resolution` `propositional-proof-complexity`

### References to cite in post

- N. Galesi, N. Talebanfard, J. Torán. *Cops-Robber Games and the Resolution of Tseitin Formulas.* TOCT 12(2), 2020. [DOI 10.1145/3378667](https://doi.org/10.1145/3378667) (ECCC TR18-170).
- N. Harvey, D. R. Wood. On the treewidth of line graphs. *Disc. Math.* 2019 (for generic tw(L(G)) bounds).

---

## Checklist before posting

- [ ] Pick stream: `#mathlib4` (infra) vs `#new members` (visibility) for Zulip A–B.
- [ ] Trim Question C if stream is Mathlib-only.
- [ ] MathOverflow: add arXiv link if we publish a preprint; otherwise keep GitHub-less / self-contained.
- [ ] Do **not** claim 2870/2870 or 383/383 as mathematical proofs — label as **computational evidence**.
- [ ] Posting walkthrough: [ZULIP_POSTING_GUIDE.md](ZULIP_POSTING_GUIDE.md)
