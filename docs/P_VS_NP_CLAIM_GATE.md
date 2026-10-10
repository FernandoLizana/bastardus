"""P vs NP claim gate — canonical Category-E filter.

The laboratory may study NP-complete problems at any evidence level.
It may present a purported **resolution** of P vs NP only if this gate passes
**and** mathematical community verification follows. Experiments alone never pass.

## Central question — exactly one path

### Camino A — prove P = NP

Deterministic algorithm that:

1. Solves an NP-complete problem.
2. Is correct on **all** inputs.
3. Always terminates.
4. Runs in \(O(n^k)\) for fixed \(k\), with \(n\) = **binary** input length.
5. Hides no exponential work in preprocessing, memory, parallelism, or huge integers.

### Camino B — prove P ≠ NP

Show some problem in NP admits **no** deterministic poly-time algorithm for all inputs:

1. Covers algorithms not yet invented.
2. Asymptotic, for arbitrarily large sizes.
3. Not limited to DPLL, CDCL, brute force, neural nets, or any single method family.

## Compatible problem families

A candidate need not ship code for every family, but must show **polynomial-size,
answer-preserving reductions** to/from a core problem covering (at least via reduction chain):

- **Logic:** SAT, CNF-SAT, 3-SAT, Circuit-SAT, NAE-3-SAT, Exact SAT, UNSAT, **TAUT** (coNP — forbids NP/coNP confusion).
- **Graphs:** Clique, IS, VC, 3-Coloring, Ham Cycle/Path, Longest Path, Steiner Tree, Dominating Set, Subgraph Iso.
- **Numbers:** Subset Sum, Partition, Knapsack, Bin Packing, Exact Cover, X3C, Set Cover, 0-1 ILP.
- **Routing/scheduling:** TSP (decision), VRP (NPC variants), Job-Shop, Timetabling, Multiprocessor, RCPSP.

## Modes

| Mode | Requirement |
|------|-------------|
| Decision | Correct YES/NO, terminates, worst-case poly if claiming P=NP |
| Search | Self-reducibility → certificates (assignment, clique, tour, subset, …) |
| Optimization | Decision ≤K → optimum via poly-many poly-size queries |
| YES and NO | Correct on satisfiable **and** unsatisfiable / no-certificate instances |

## Errors that must be discarded

See `ERROR_DISCARDS` in `backend/claim_gate/catalog.py` (brute \(2^n\), input-dependent exponents, exp tables/memory/parallelism/bits, unary vs binary, pseudo-poly, treewidth-only, clause-ratio-only, almost-always, distribution-dependent, unremoved error probability, neural nets without proof, nontermination, small-\(n\) curve fitting, practice≠asymptotics).

Official reminder: poly-time on “most” inputs would **not** settle worst-case P vs NP.

## Barriers

| Barrier | Gate demand |
|---------|-------------|
| Relativization (BGS 1975) | Non-relativizing step identified |
| Natural proofs (RR 1997) | Constructive / large / useful checked; or crypto assumptions addressed |
| Algebrization (AW 2008) | Non-algebrizing step identified |
| Restricted models | Monotone / AC⁰ / fixed depth / tree-like / DPLL / CDCL / … alone insufficient |

## Consequences (must acknowledge)

- **If A:** all NPC in P; search in P; P=NP=coNP; TAUT/UNSAT in P; exact opt often poly; classical OWFs collapse; crypto foundations break; \(O(n^{1000})\) still counts.
- **If B:** does **not** imply all NPC need exp time; factoring hard; crypto safe; NP≠coNP; average-case hard; no approx/heuristics; quantum cannot help. Only: no det. poly algorithm for all NP on all inputs.

## Machine-checkable API

```text
GET  /claims/p-vs-np/catalog
GET  /claims/p-vs-np/template?side=A_P_eq_NP|B_P_ne_NP
POST /claims/p-vs-np/gate   # body: ClaimDossier JSON → GateReport
```

`may_present_as_resolution=true` requires full checklist + E6 + Lean artifacts + ≥2 independent reviewers.
Even then the report disclaimer states this is **process**, not a Clay-ready theorem.

## Hard laboratory rule

Nothing below **E5**, and no dossier failing this gate, may be labelled a P vs NP resolution.
"""
