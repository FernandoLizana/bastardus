# Research gaps (extracted / inferred only from checked sources)

**Policy:** Items marked `EXPLICIT_IN_SOURCE` quote or closely paraphrase an open problem stated in a primary/secondary source we inspected. Items marked `INFERRED_GAP` are limitations we observe from contrasting results — **not** claims that authors wrote that exact sentence.

Evidence tags for this document itself: literature synthesis (historiador), not a theorem.

## Explicit / near-explicit open problems

1. **EXPLICIT_IN_SOURCE (JAIR 2023 / related AAAI discussion line):** A *complete characterization* of (general) resolution complexity of Tseitin formulas in terms of treewidth — unlike regular resolution, where poly-size ↔ `tw = O(log n)` for bounded degree — is described in the literature as still incomplete / open for general resolution.  
   *Difficulty:* High. *Novelty potential:* High if resolved. *Experimentable:* Medium (small-n exact metrics). *Formalizable:* Medium. *P vs NP relevance:* Low–medium (restricted system).

2. **EXPLICIT_IN_SOURCE (BSW / Atserias–Bonet optimality line):** Whether size–width tradeoffs can be improved toward *subpolynomial* relations. Optimality results show this is tightly constrained.  
   *Difficulty:* Very high. *Novelty:* Low remaining room. *Exp:* Hard. *Formal:* Hard. *PvsNP:* Low.

3. **INFERRED_GAP (JAIR 2023 cites Galesi et al. 2020 + BSW):** For *general* resolution size of Tseitin, available width→size pipeline yields roughly `2^{Ω(tw²/n)}`, tight at linear tw, but **mid-range treewidth** (e.g. `tw = n^α`, `0<α<1`) may leave quantitative gaps vs regular-resolution `2^{Θ(tw)}` technology.  
   *Difficulty:* High. *Novelty:* Medium–high for sharper constants/exponents. *Exp:* Medium. *Formal:* Hard. *PvsNP:* Low.

4. **INFERRED_GAP (SAT 2022 tight bounds paper):** Residual factors involving `Δ`, line-graph treewidth `tw(L(G))`, and log terms in upper/lower bounds for some models.  
   *Difficulty:* Medium–high. *Novelty:* Medium (constant/factor cleanup). *Exp:* Medium. *Formal:* Medium. *PvsNP:* Low.

5. **INFERRED_GAP (arXiv:2402.00542):** Encoding / variable-order phenomena for parity: resolution hard while DRAT short — systematize which reorderings maximize tw.  
   *Difficulty:* Medium. *Novelty:* Medium. *Exp:* High. *Formal:* Medium. *PvsNP:* Low.

6. **EXPLICIT_IN_SOURCE (Atserias–Dalmau applications aside):** Width characterization via pebble games — computational complexity of *exact* min width for structured families; practical certified width oracles.  
   *Difficulty:* Medium. *Novelty:* Medium (engineering + lemmas). *Exp:* High. *Formal:* High. *PvsNP:* Low.

7. **INFERRED_GAP:** Exact closed-form `Width(T(G,c))` for graph products, lifts, barbells, and modular join graphs under odd charge — beyond asymptotic expander theorems.  
   *Difficulty:* Medium. *Novelty:* Potentially high for *exact* combinatorial identities. *Exp:* High (small n). *Formal:* Medium. *PvsNP:* Very low.

8. **INFERRED_GAP:** Trade-offs width / clause-space / depth specifically for Tseitin on non-regular degree sequences.  
   *Difficulty:* High. *Novelty:* Medium. *Exp:* Medium. *Formal:* Hard. *PvsNP:* Low.

9. **INFERRED_GAP:** Tree-like vs regular vs general resolution *width* (not only size) gaps for the same Tseitin instance.  
   *Difficulty:* Medium–high. *Novelty:* Medium. *Exp:* High for tiny n. *Formal:* Medium. *PvsNP:* Low.

10. **SECONDARY (Frege Tseitin):** Lifting expander-Tseitin hardness further into stronger Frege fragments — active but outside our sprint.  
    *Difficulty:* Very high. *Novelty:* High. *Exp:* Low. *Formal:* Hard. *PvsNP:* Medium (still not P≠NP).

11. **PHP classic:** Further restricted PHP encodings (BSW already treats some).  
    *Difficulty:* High. *Novelty:* Low–medium. *Exp:* Medium. *Formal:* Medium. *PvsNP:* Low.

12. **INFERRED_GAP:** Minimal width as a function of pathwidth vs treewidth for series-parallel Tseitin graphs.  
    *Difficulty:* Medium. *Novelty:* Medium. *Exp:* High. *Formal:* Medium. *PvsNP:* Low.

13. **INFERRED_GAP:** Bottleneck graphs (two expanders + few bridges): is width governed by bridge cut or by expander cores?  
    *Difficulty:* Medium. *Novelty:* Medium–high. *Exp:* High. *Formal:* Medium. *PvsNP:* Low.

14. **INFERRED_GAP:** Evolutionary search for graphs maximizing `Width / tw` ratio — seek outliers to known asymptotic regimes.  
    *Difficulty:* Low–medium (compute). *Novelty:* Unknown until histograms exist. *Exp:* Very high. *Formal:* Later. *PvsNP:* None.

15. **INFERRED_GAP:** Certified optimality of width (closure certificate) vs pebble-game certificates — equivalence checks on data.  
    *Difficulty:* Medium. *Novelty:* Low (expected match) but good validation. *Exp:* High. *Formal:* High. *PvsNP:* None.

16. **Polynomial Calculus / Cutting Planes vs Tseitin:** known separations exist; exact small-n comparisons for gadget graphs underdocumented computationally.  
    *Difficulty:* High. *Novelty:* Medium. *Exp:* Medium. *Formal:* Hard. *PvsNP:* Low.

17. **INFERRED_GAP:** Monotone circuit / AC0 exact synthesis for parity-related functions as parallel Line 2 — not Tseitin proofs.  
    *Difficulty:* High. *Novelty:* Medium. *Exp:* Medium. *Formal:* Medium. *PvsNP:* barrier-heavy.

18. **Automatizability:** Resolution not automatizable under complexity assumptions (Alekhnovich–Razborov line) — any “width search proves P=NP” idea is blocked.  
    *Difficulty:* N/A. *Novelty:* Guardrail. *Exp:* N/A. *Formal:* N/A. *PvsNP:* **Barrier reminder**.

19. **Relativization / natural proofs:** Direct P≠NP via Tseitin resolution LBs cannot work — resolution is a *restricted* system.  
    *Difficulty:* N/A. *Novelty:* Guardrail. *PvsNP:* Separates Line 1 from Line 3.

20. **INFERRED_GAP:** Precise constants in `Width(T(G,c)) ≥ f(tw(G), Δ)` for Δ≤3 — sharpen Galesi-style bounds on small instances then conjecture.  
    *Difficulty:* Medium. *Novelty:* Medium if constants improve known inequalities. *Exp:* High. *Formal:* Medium–hard. *PvsNP:* Very low.

## Candidate selection (sprint)

| ID | Candidate | Importance | Realism | Compute fit |
|----|-----------|------------|---------|-------------|
| A | Sharper mid-range general-resolution size via better width analysis | High | Low this sprint | Medium |
| B | Exact Width↔structural law on bottleneck / modular joins | Medium | High | High |
| C | Prove weak exact Width law for trees / cycles / series-parallel | Medium | **Highest** | High |

**Selected primary for this sprint: Candidate C → B**, with A as long-term.

Reason: (C) can yield an R4–R5 lemma with certificates; (B) is the experimental search direction for a falsable R2 conjecture; (A) needs theory beyond pilot scale and overlaps heavily with known asymptotics.
