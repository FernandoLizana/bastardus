# Literature review: Tseitin resolution width vs treewidth / line graph

**Date:** 2026-08-02  
**Scope:** Exact theorem statements for Ben-Sasson–Wigderson (2001), de Colnet–Mengel (JAIR 2021), Itsykson–Riazanov–Smirnov (SAT 2022); width characterization via line-graph treewidth; Mathlib v4.32.0 gaps; Zulip/community notes; risk assessment for PNPLab ChordWidth pivot.  
**Related:** [CHORD_DIAGRAM_TSEITIN_WIDTH.md](../papers/CHORD_DIAGRAM_TSEITIN_WIDTH.md), [CHORD_WIDTH_LEAN_STATUS.md](CHORD_WIDTH_LEAN_STATUS.md)

---

## Executive summary

| Question | Answer |
|----------|--------|
| **Key width theorem (PNPLab hypothesis)** | **Not** in Ben-Sasson–Wigderson, de Colnet–Mengel, or SAT 2022. Exact formula is **Galesi–Talebanfard–Torán (TOCT 2020)**: \(w(T(G,c)\vdash) = \max\{\Delta(G), \mathrm{tw}(L(G))\}\). |
| **What the three named papers actually prove** | BSW: width↔size + expansion width lower bounds. de Colnet–Mengel: **regular-resolution size** \(2^{\Theta(\mathrm{tw}(G))}\) iff-log characterization. Itsykson et al.: **tight size** lower bound \(2^{\Omega(\mathrm{tw}(G))}\) for regular resolution / OBDD. |
| **Cycle + two chords covered?** | **No explicit case study** in any cited paper. Covered **indirectly** by Galesi width formula + \(\mathrm{tw}(L(G))\) bounds on Δ=3 outerplanar vs crossing families. |
| **Mathlib v4.32.0** | `SimpleGraph.lineGraph` **present**; `treeWidth` / `TreeDecomp` **absent** (open PR #38334, not in v4.32.0 pin). |

---

## 1. Paper map (what each source contributes)

```
                    ┌─────────────────────────────────────┐
                    │  Galesi–Talebanfard–Torán (TOCT 2020) │
                    │  w(T) = max(Δ, tw(L(G)))  ◄── WIDTH │
                    └──────────────┬──────────────────────┘
                                   │ used with BSW width↔size
         ┌─────────────────────────┼─────────────────────────┐
         ▼                         ▼                         ▼
  Ben-Sasson–Wigderson      de Colnet–Mengel           Itsykson et al.
  (2001)                    (JAIR 2021)                (SAT 2022)
  width ↔ size              SIZE 2^{Θ(tw(G))}           SIZE 2^{Ω(tw(G))}
  expansion ≥ width         regular resolution         tight; removes log|V|
```

PNPLab's `TseitinWidthTreewidthCharacterization` is the **Galesi et al. width theorem**, not an original result. The three papers named in the project brief are **supporting** (size, automatizability, treewidth parameter) but do not state the width = max(Δ, tw(L(G))) identity themselves.

---

## 2. Ben-Sasson & Wigderson (2001)

**Reference:** Eli Ben-Sasson and Avi Wigderson. *Short Proofs Are Narrow—Resolution Made Simple.* JACM 48(3):517–535, 2001. [DOI 10.1145/375827.375835](https://doi.org/10.1145/375827.375835). Preprint: [people.inf.ethz.ch PDF](https://people.inf.ethz.ch/emo/SatSem05/Papers/BensassonWigderson01.pdf).

### 2.1 Hypotheses (global)

- Resolution proof system; width = max clause width in proof.
- Tseitin: connected graph \(G\), odd marking \(f : V(G) \to \{0,1\}\) (sum of charges ≡ 1 mod 2), one variable per edge, parity constraint per vertex.

### 2.2 Exact theorems (quoted)

**Width–size (tree-like resolution).**

> **Theorem 3.3.** \(w(F \vdash 0) \le w(F) + \log S_T(F)\).

> **Corollary 3.4.** \(S_T(F) \ge 2^{(w(F\vdash 0) - w(F))}\).

**Width–size (general resolution).**

> **Theorem 3.5.** \(w(F \vdash 0) \le w(F) + O(\sqrt{n \ln S(F)})\).

> **Corollary 3.6.** \(S(F) \ge \exp\left(\Omega\left(\dfrac{(w(F\vdash 0) - w(F))^2}{n}\right)\right)\).

**Tseitin width lower bound (expansion, not treewidth).**

> **Theorem 4.4.** For \(G\) a connected graph and \(f\) an odd-weight function on \(V(G)\), \(w(\tau(G,f) \vdash 0) \ge e(G)\),

where the **expansion** is

\[
e(G) = \min\bigl\{|E(V', V\setminus V')| : V' \subseteq V,\ |V|/3 \le |V'| \le 2|V|/3\bigr\}.
\]

> **Corollary 4.5 [Urquhart 1987].** For \(G\) a 3-regular connected expander with \(e(G) = \Omega(|V|)\) and \(f\) odd-weight, \(S(\tau(G,f)) = 2^{\Omega(|\tau(G,f)|)}\).

### 2.3 Relevance to PNPLab

- Provides the **machinery** to lift width lower bounds to exponential **size** lower bounds (Corollary 3.6).
- Tseitin **width** lower bound is **expansion-based**, not treewidth- or line-graph-based.
- Does **not** characterize \(w(T(G,c)\vdash)\) as \(\max(\Delta, \mathrm{tw}(L(G)))\).

---

## 3. Galesi, Talebanfard & Torán (2020) — width characterization

**Reference:** Nicola Galesi, Navid Talebanfard, Jacobo Torán. *Cops-Robber Games and the Resolution of Tseitin Formulas.* **TOCT** 12(2), 2020. [DOI 10.1145/3378667](https://doi.org/10.1145/3378667). ECCC: [TR18-170](https://eccc.weizmann.ac.il/report/2018/170/).

This is the **primary source** for PNPLab's literature hypothesis (often cited as Corollaries 8 and 16 in the ECCC version).

### 3.1 Exact width theorem

> **Theorem (Galesi–Talebanfard–Torán; Corollaries 8 & 16, ECCC TR18-170).**  
> Let \(G(V,E)\) be a graph and \(T(G,c)\) an **unsatisfiable** Tseitin formula. Then
\[
w(T(G,c)) = \max\bigl\{\mathrm{tw}(L(G)),\ \Delta(G)\bigr\},
\]
where \(L(G)\) is the **line graph** (vertices = edges of \(G\); adjacency = share a vertex), \(\Delta(G)\) maximum degree, and \(w(T(G,c))\) is resolution refutation width.

**Hypotheses:** unsatisfiable Tseitin on \(G\); connectedness handled per component in full paper; cop-robber game characterization of width/depth/variable space.

### 3.2 Line graph vs primal treewidth

> **Proposition (folklore; cited in Itsykson et al. and follow-ups).**  
> \(\tfrac{1}{2}(\mathrm{tw}(G)+1)-1 \le \mathrm{tw}(L(G)) \le (\mathrm{tw}(G)+1)\cdot\Delta(G)-1\).

For **constant Δ**, \(\mathrm{tw}(L(G)) = \Theta(\mathrm{tw}(G))\) up to constant factors — but the **width formula uses tw(L(G))**, not tw(G) directly.

### 3.3 Related bounds (same paper)

- Resolution width, depth, and variable space for Tseitin coincide **up to a logarithmic factor**.
- Davis–Putnam resolution is **optimal** for these measures on Tseitin.

---

## 4. de Colnet & Mengel (JAIR 2021)

**Reference:** Alexis de Colnet, Stefan Mengel. *Characterizing Tseitin-Formulas with Short Regular Resolution Refutations.* **JAIR** 76, 2023 (arXiv 2103.09609, March 2021). [DOI 10.1613/jair.1.13521](https://doi.org/10.1613/jair.1.13521).

### 4.1 Main theorem (SIZE, not width)

> **Theorem 1.1.** Let \(T(G,c)\) be an unsatisfiable Tseitin-formula where \(G\) is connected with maximum degree at most \(\Delta\). The length of the smallest **regular resolution** refutation of \(T(G,c)\) is at least
\[
2^{\Omega(\mathrm{tw}(G)/\Delta)} \cdot |V(G)|^{-1}.
\]

### 4.2 Characterization theorem

> Classes of bounded-degree unsatisfiable Tseitin formulas have **polynomial-length regular resolution refutations if and only if** \(\mathrm{tw}(G) = O(\log |V(G)|)\) for all graphs in the class.

### 4.3 Proof architecture

1. Reduce unsatisfiable Tseitin refutation length → DNNF size for a **satisfiable** Tseitin on the same \(G\) (Theorem 3.1; improves Itsykson et al. 2021 1-BP reduction).
2. Prove DNNF lower bound \(2^{\Omega(\mathrm{tw}(G))}\) for satisfiable Tseitin (Lemma 13 / Theorem 4.1 in arXiv numbering).

### 4.4 Relation to width hypothesis

- Uses **tw(G)** (primal), not tw(L(G)), for **size** lower bounds.
- Explicitly notes prior width-based route: combining Ben-Sasson (2002) width–size with Galesi et al. width bounds yields \(2^{\Omega(\mathrm{tw}(G)^2)/|V|}\) for general resolution when tw is large.
- **Does not** state \(w = \max(\Delta, \mathrm{tw}(L(G)))\).

---

## 5. Itsykson, Riazanov & Smirnov (SAT 2022)

**Reference:** Dmitry Itsykson, Artur Riazanov, Petr Smirnov. *Tight Bounds for Tseitin Formulas.* **LIPIcs SAT 2022**, 6:1–6:21. [DOI 10.4230/LIPIcs.SAT.2022.6](https://doi.org/10.4230/LIPIcs.SAT.2022.6).

### 5.1 Main lower bounds (SIZE)

> **Theorem 3.1.** Let \(G\) be a connected graph and \(T(G,c)\) unsatisfiable. Any OBDD(\(\land\), reordering) refutation has size \(\ge 2^{\Omega(\mathrm{tw}(G))}\).

> **Theorem 4.3.** Let \(G\) be connected and \(T(G,c)\) unsatisfiable. Any **regular resolution** refutation has size \(\ge 2^{\Omega(\mathrm{tw}(G))}\).

> **Theorem 4.1.** Let \(T(G,c)\) be satisfiable and \(D\) a DNNF computing it. Then \(|D| \ge 2^{\Omega(\mathrm{tw}(G))}\).

### 5.2 Upper bounds (tightness)

- Matching upper bound \(2^{O(\mathrm{tw}(G))}\) for DNNF (Theorem 4.4).
- Regular resolution upper bound: \(\mathrm{poly}(T(G,c)) \cdot 2^{O(\mathrm{tw}(L(G)))}\) [Alekhnovich–Razborov 2011, cited as [1]].
- **Almost automatability:** regular resolution and OBDD(\(\land\),reordering) on Tseitin in time \(2^{O(\mathrm{tw}(G)\log|T(G,c)|)}\).

### 5.3 Improvement over prior work

- Removes \(\log |V(G)|\) factor from exponent compared to Itsykson et al. (Comput. Complex. 2021): \(2^{\Omega(\mathrm{tw}(G)/\log|V|)} \to 2^{\Omega(\mathrm{tw}(G))}\).
- Improves de Colnet–Mengel's \(2^{\Omega(\mathrm{tw}(G)/\Delta)}/|V|\) by removing \(/\Delta\) in exponent (for the size lower bound).

### 5.4 Line graph mention

Paper uses tw(L(G)) only for **upper bounds / automatizability** (BWBATP), not for exact width. Family \(G_{n,k}\) with \(\mathrm{tw}(L(G_{n,k})) = 4n + O(k^3)\) shows tw(L(G)) can exceed tw(G) substantially.

---

## 6. Cycle + two chords: literature coverage

### 6.1 Direct coverage

**None** of Ben-Sasson–Wigderson, de Colnet–Mengel, or Itsykson et al. analyze \(C_n\) plus two chords, crossing vs noncrossing pairings, or the PNPLab crossing law (Width = 3 vs 4 at Δ = 3).

### 6.2 Indirect coverage (recommended proof route)

| Step | Source | Content |
|------|--------|---------|
| 1 | Galesi et al. | \(\mathrm{Width}(T(G,\varphi)) = \max(3, \mathrm{tw}(L(G)))\) for Δ=3 |
| 2 | Harvey–Wood / line-graph literature | Bounds on \(\mathrm{tw}(L(G))\) from primal structure |
| 3 | Outerplanar graph theory | Noncrossing two-chord graphs are outerplanar ⇒ \(\mathrm{tw}(G) \le 2\) ⇒ \(\mathrm{tw}(L(G)) \le O(\Delta \cdot \mathrm{tw}(G)) = O(1)\) |
| 4 | PNPLab Phase 3 | Crossing case: suppressed core ≅ \(K_4\) ⇒ \(\mathrm{tw}(L(G)) \ge 2\) (target ≥ 3 on line graph of K₄ region) ⇒ width 4 |

**Expected values (PNPLab conjecture, not literature theorem):**

| Pairing | Geometry | tw(L(G)) (expected) | Width |
|---------|----------|---------------------|-------|
| Disjoint / nested | Noncrossing | ≤ 2 | 3 |
| Crossing | \(K_4\) minor in core | ≥ 3 | 4 |

### 6.3 Odd marking

All Tseitin width theorems are stated for **unsatisfiable** instances; width depends on \(G\) and unsatisfiability pattern, not on the specific charge function beyond satisfiability/unsatisfiability per component. For connected \(G\), any odd marking yields unsatisfiable Tseitin; Galesi width is independent of which odd marking (game characterization is graph-only).

---

## 7. Mathlib v4.32.0 status

**Project pin:** `lean/lakefile.toml` → `mathlib` rev **`v4.32.0`**.

### 7.1 Available

| Declaration | Module | Notes |
|-------------|--------|-------|
| `SimpleGraph.lineGraph` | `Mathlib.Combinatorics.SimpleGraph.LineGraph` | Merged PR [#16276](https://github.com/leanprover-community/mathlib4/pull/16276), Sept 2024 |
| `lineGraph_adj_iff_exists` | same | Adjacency = share vertex |
| `Iso.lineGraph`, containment lemmas | same | Used in PNPLab `LineGraph.lean` |
| `SimpleGraph.IsTree`, acyclicity | `Mathlib.Combinatorics.SimpleGraph.Acyclic` | Trees tw = 1 convention |

### 7.2 Not in v4.32.0

| Needed for ChordWidth | Status |
|------------------------|--------|
| `TreeDecomp`, `SimpleGraph.treeWidth` | **Absent.** Open PR [#38334](https://github.com/leanprover-community/mathlib4/pull/38334) (Apr 2026, assigned YaelDillies; `awaiting-author` cycles). Follow-up [#39939](https://github.com/leanprover-community/mathlib4/pull/39939) (cliqueNum ≤ treeWidth) depends on it. |
| `tw(L(G))` bounds | **No API** |
| Line graph treewidth theory | **Not formalized** |
| `IsOuterplanar` / Whitney ears | **Absent** (PNPLab audit §3.6) |
| Resolution / proof complexity | **Outside Mathlib** |
| Cop-robber / Tseitin width game | **Not formalized** |

PNPLab uses `TreewidthWitness` Prop stub in `PNPLab.ChordWidth.Treewidth` — correct for v4.32.0.

### 7.3 Upgrade path

When PR #38334 merges: import `Mathlib.Combinatorics.SimpleGraph.TreeDecomp`, replace stub with `G.treeWidth`. Still need **project-specific** lemmas: tw(K₄), tw(C₄), tw(L(G)) for two-chord families, degree-2 suppression.

---

## 8. Community recommendations (Zulip / Mathlib)

Sources: [Mathlib graph-theory stream index](https://leanprover-community.github.io/archive/stream/252551-graph-theory/index.html), PR #38334 review thread, contributor guidelines.

| Topic | Recommendation |
|-------|----------------|
| **New graph API** | Introduce on [leanprover.zulipchat.com](https://leanprover.zulipchat.com/) (#graph theory / #mathlib4); mention PR per [contribution guidelines](https://leanprover-community.github.io/contribute/index.html). |
| **TreeDecomp design** | Reviewer **YaelDillies** (PR #38334): consider generalizing to **pathwidth** before merge — either `GraphDecomposition` base + subtypes, or `PathDecomp` as subtype of `TreeDecomp`. |
| **Treewidth in Zulip** | No dedicated treewidth thread found in graph-theory archive (Jan 2026). Active topics: connectivity, matchings, Turán, minors — **treewidth is greenfield**. |
| **Line graph** | Landed quietly via PR #16276; no Zulip design debate archived. |
| **PNPLab strategy** | Do **not** block on Mathlib treewidth for Phase 1–2; use stub + external Python verification (`chord_treewidth_verification.csv`). Revisit after #38334 merge or pin newer Mathlib. |

---

## 9. Risk assessment

| Risk | Severity | Mitigation |
|------|----------|------------|
| **Wrong attribution** — hypothesis credited to BSW / de Colnet / Itsykson instead of Galesi et al. | **High** | Cite Galesi TOCT 2020 as width source; others for size/tightness only. |
| **Width vs size conflation** — de Colnet / Itsykson bound **refutation length**, not clause width | **High** | Keep `LiteratureHypothesis` separate from size corollaries. |
| **tw(G) vs tw(L(G))** — size papers use primal tw; width uses line graph | **Medium** | Prove tw(L(G)) bounds explicitly for two-chord graphs; do not assume tw(G)=tw(L(G)). |
| **Mathlib gap** — no treeWidth in v4.32.0 | **Medium** | Stub witnesses; Python cross-check; plan Mathlib upgrade. |
| **Cycle+two-chords not in literature** — crossing law is PNPLab contribution | **Medium** | Conditional theorems only; Phase 3 core iso + tw bounds are original graph work. |
| **Expansion vs tw** — BSW Theorem 4.4 doesn't give width=4 for crossing case directly | **Low** | Use Galesi formula, not BSW expansion, for width predictions. |
| **Unsatisfiability / odd φ** — smoke tests use single-bit charge | **Low** | Generalize to all odd markings (folklore: width independent of marking for connected G). |

**Gate for Phase 3 (from CHORD_WIDTH_LEAN_STATUS):** Python treewidth verification (n=5..100) + this literature cross-check must agree before investing in elimination-order proofs.

---

## 10. Bibliography

1. Eli Ben-Sasson, Avi Wigderson. Short Proofs Are Narrow—Resolution Made Simple. *JACM* 48(3):517–535, 2001. [doi:10.1145/375827.375835](https://doi.org/10.1145/375827.375835)

2. Nicola Galesi, Navid Talebanfard, Jacobo Torán. Cops-Robber Games and the Resolution of Tseitin Formulas. *TOCT* 12(2), 2020. [doi:10.1145/3378667](https://doi.org/10.1145/3378667). ECCC TR18-170.

3. Alexis de Colnet, Stefan Mengel. Characterizing Tseitin-Formulas with Short Regular Resolution Refutations. *JAIR* 76, 2023. [doi:10.1613/jair.1.13521](https://doi.org/10.1613/jair.1.13521). arXiv:2103.09609.

4. Dmitry Itsykson, Artur Riazanov, Petr Smirnov. Tight Bounds for Tseitin Formulas. *LIPIcs* 236 (SAT 2022), 6:1–6:21. [doi:10.4230/LIPIcs.SAT.2022.6](https://doi.org/10.4230/LIPIcs.SAT.2022.6)

5. Dmitry Itsykson, Artur Riazanov, Danil Sagunov, Petr Smirnov. Near-Optimal Lower Bounds on Regular Resolution Refutations of Tseitin Formulas. *Computational Complexity* 30(2):13, 2021.

6. Mikhail Alekhnovich, Alexander Razborov. Resolution is Not Automatizable Unless W[P] is Tractable. *SIAM J. Comput.* 40(4):1165–1215, 2011.

7. Grigorii S. Tseitin. On the Complexity of Derivation in Propositional Calculus. *Studies in Constructive Mathematics and Mathematical Logic*, 1968.

8. David Harvey, David R. Wood. The treewidth of line graphs. *J. Combinatorial Theory B* 134:157–174, 2019.

9. PNPLab: `reports/CROSSING_LAW_SOUNDNESS_AUDIT.md`, `reports/CHORD_WIDTH_LEAN_STATUS.md`.

---

## 11. Key theorem quote (for parent agent)

> **Galesi–Talebanfard–Torán (TOCT 2020):** For unsatisfiable Tseitin \(T(G,c)\), resolution refutation width satisfies  
> **\(w(T(G,c)) = \max\{\mathrm{tw}(L(G)),\ \Delta(G)\}\).**

Supporting size quote (Itsykson SAT 2022):

> **\(S_R(T(G,c)) \ge 2^{\Omega(\mathrm{tw}(G))}\)** for connected \(G\) (tight up to poly factors).
