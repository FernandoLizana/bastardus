# Roadmap

## Phase 0 — Analysis ✅ (this MVP bootstrap)

Architecture, ADRs, risks, acceptance criteria.

## Phase 1 — Mathematical core ✅ (MVP)

CNF/3-CNF, certificates, verifiers.

## Phase 2 — Solvers ✅ (MVP)

Brute force, DPLL, PySAT adapter.

## Phase 3 — Reductions ✅ (expanded)

- SAT → 3-SAT
- 3-SAT → Clique
- 3-SAT → Independent Set
- 3-SAT → Vertex Cover
Empirical cross-checks with Hypothesis (E2). Lean proofs still pending.

## Phase 4 — Experiments ✅ (MVP)

Random 3-SAT phase-transition study + reports.

## Phase 5 — Conjectures ✅ (refutation search)

Store + automatic minimal counterexample search (`backend/conjectures/refute.py`).

## Phase 6 — Audit ✅ (MVP heuristics)

`proof_auditor` + `research_barriers`.

## Phase 7 — UI 🔄

Dashboard panels: Inicio, Solvers, Generador, Reducciones, Conjeturas, Auditor, Barreras.

## Phase 8 — Lean formalization 🔄

Certificate checkers + small lemmas in `lean/PNPLab/` (`Certificates.lean`,
`IndependentSet.lean`). Linked from `backend/formalization` (E5-partial).
Karp reduction correctness proofs still pending.

## Generators added

- pigeonhole (PHP)
- Tseitin (odd charge ⇒ UNSAT)
- hard / planted Subset Sum (+ pseudo-poly DP warning)
- crafted Hamiltonian (ham / non-ham)

## Reductions added

- Hamiltonian Cycle → TSP decision


## Phase 9 — Scientific docs ✅ (initial)

Foundations, methodology, barriers, reproducibility, paper template.

## Also landed

- Adaptive **MetaSolver** (practical selection only; ≤ E2; never claims P).


## Non-goals (near term)

- Claiming P vs NP resolution
- Submitting to Clay Mathematics Institute
- Treating CDCL industrial performance as theory
