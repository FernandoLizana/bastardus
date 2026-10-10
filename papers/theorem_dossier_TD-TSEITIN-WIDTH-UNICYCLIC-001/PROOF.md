# TD-TSEITIN-WIDTH-UNICYCLIC-001 — Width = Δ for Tseitin on unicyclic graphs

**Status:** constructive certificates (Python), mass-checked on small families (E2/E4).  
**Not** a P vs NP claim. Resolution-restricted.

## Statement

Let \(G\) be a connected simple **unicyclic** graph (exactly one cycle; \(|E|=|V|\ge 3\))
and \(c:V\to\{0,1\}\) with \(\sum_v c(v)\) odd. Let \(T(G,c)\) be the Tseitin CNF and
\(\Delta=\Delta(G)\). Then the minimum resolution width satisfies

\[
\operatorname{Width}(T(G,c))=\Delta.
\]

## Proof sketch (constructive)

1. **Leaf peeling** (same Unit–XOR lemma as for trees): while a degree-1 vertex \(u\) exists,
   derive a unit on the unique incident edge and reduce the XOR at its neighbour, updating
   the charge. All derived clauses have width \(\le\Delta\).
2. After removing all pending trees, the residual graph is the unique cycle with some
   odd total charge (parity invariant).
3. **Width-2 saturation** on the residual cycle yields \(\bot\). Since \(\Delta\ge 2\) for
   unicyclic \(n\ge 3\),    this stays within width \(\Delta\).
4. **Matching lower bound:** axiom width is \(\Delta\) (a maximum-degree vertex contributes
   XOR clauses of width \(\Delta\)), hence \(\operatorname{Width}\ge\Delta\).

Implementation: `build_unicyclic_tseitin_refutation` in
`backend/proof_complexity/constructive_proofs.py` (machine-checked parent pointers).

## Evidence

- Unit tests: path+chord families, cycle+pendant; exact width oracle agreement.
- Frontier native: 768 unicyclic n≤5 with W=Δ (unit charge, Δ-bounded).
- Prior: trees and cycles already certified; this interpolates them.

## Barriers / claim gate

Fails Camino B: restricted proof system (resolution). Category C/D lemma only.

## Open tightening

- Full Aut-orbit odd charges on all labeled unicyclic up to larger n (native).
- Lean induction formalization of the peel+cycle composition.
- Δ-unbounded unicyclic (still expected; peel argument does not need Δ≤3).
