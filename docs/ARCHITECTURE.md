# Architecture — PNP Research Laboratory

## Goals

Build a modular research platform that separates:

- **experimental code** (solvers, generators, benchmarks);
- **mathematical specification** (docs + models);
- **formalization** (Lean 4);
- **human documentation** (papers, methodology).

## High-level diagram

```text
┌─────────────┐     ┌──────────────┐     ┌─────────────────┐
│  Frontend   │────▶│  FastAPI     │────▶│  Solvers / gens │
│  React/Vite │     │  backend/api │     │  reductions     │
└─────────────┘     └──────┬───────┘     └────────┬────────┘
                           │                      │
                           ▼                      ▼
                    ┌──────────────┐     ┌─────────────────┐
                    │ Conjectures  │     │ Experiments     │
                    │ Barriers     │     │ Parquet/CSV/MD  │
                    │ ProofAuditor │     │ metrics E≤E2    │
                    └──────────────┘     └─────────────────┘
                           │
                           ▼
                    ┌──────────────┐
                    │ lean/        │  (E5 target; Phase 8)
                    └──────────────┘
```

## Package map

| Path | Role |
|------|------|
| `backend/models` | CNF, certificates, problem IR |
| `backend/solvers` | Brute force, DPLL, PySAT, … |
| `backend/generators` | Reproducible instance families |
| `backend/reductions` | Verifiable Karp-style reductions |
| `backend/experiments` | Benchmarks & reports |
| `backend/complexity` | Scaling analysis (warn: no auto P∈) |
| `backend/conjectures` | Conjecture DB + refutation-first |
| `backend/proof_auditor` | Heuristic proof critique |
| `backend/research_barriers` | Barrier checklists |
| `backend/api` | HTTP API |
| `lean/` | Lean 4 formalization |
| `frontend/` | Dashboard |
| `docs/` | Scientific & engineering docs |

## ADR-001: Python-first research core

**Decision:** Implement the research core in Python 3.11+ with typed models (dataclasses/Pydantic).

**Rationale:** Fast iteration for solvers/experiments; rich scientific ecosystem; Lean remains the formal side-car.

**Consequences:** Performance-critical CDCL remains via PySAT; we do not reimplement industrial CDCL in pure Python for the MVP.

## ADR-002: Evidence tags on every result

**Decision:** Every `SolverResult`, report, and conjecture carries an `EvidenceLevel` and `claim_type`.

**Rationale:** Prevent accidental presentation of E2 observations as theorems.

## ADR-003: Refutation-first conjecture workflow

**Decision:** Status cannot leave `idea` without a barrier checklist; automated search prioritizes counterexamples.

## ADR-004: No automatic asymptotic classification

**Decision:** Benchmarks may fit curves for *descriptive* comparison but must not conclude membership in P.

## Risks

| Risk | Mitigation |
|------|------------|
| Overclaiming from plots | Hard policy + report templates |
| Solver bugs | Cross-validation + Hypothesis |
| Flaky PySAT installs | Optional path + CI wheel checks |
| Scope explosion | Phased roadmap; MVP gate |

## Acceptance criteria (Phase 0–MVP gate)

- [x] CNF model + verifier
- [x] Brute force + DPLL + PySAT
- [x] Random 3-SAT generator
- [x] Instrumented metrics
- [x] Phase-transition experiment report with P vs NP disclaimer
- [x] Tests incl. property-based
- [x] Docker Compose skeleton
- [x] Documentation set
