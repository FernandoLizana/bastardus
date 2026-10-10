# Phase Transition Experiment Report (Evidence Level E2)

**Timestamp (UTC):** 20260714T021746Z
**n (variables):** 15
**Ratios α tested:** [2.0, 3.0, 3.5, 4.0, 4.2, 4.5, 5.0, 6.0]
**Instances per ratio:** 20
**Base seed:** 12345
**Solvers:** ['dpll', 'pysat']
**Solver disagreements:** 0

## Claim type

`observation_experimental` — **not** a lemma, **not** a proof.

## What we measured

For each α = m/n we generated uniform-ish random 3-CNF instances (no tautological clauses) and ran independent solvers, recording satisfiability (when decided), wall/CPU time, decisions, backtracks, and memory proxies.

## Summary table (empirical sat. rate)

| α | sat. rate (pysat if available) | median decisions (dpll) |
|---|---|---|
| 2.0 | 1.000 | 3.0 |
| 3.0 | 1.000 | 5.0 |
| 3.5 | 1.000 | 5.5 |
| 4.0 | 0.850 | 5.5 |
| 4.2 | 0.700 | 6.0 |
| 4.5 | 0.750 | 5.0 |
| 5.0 | 0.350 | 6.0 |
| 6.0 | 0.100 | 6.0 |

## Why this does **not** demonstrate P = NP or P ≠ NP

1. **Finite n only.** Asymptotic class membership is a statement about all sufficiently large inputs. Any experiment on fixed n is consistent with infinitely many asymptotic regimes (barrier: finite vs asymptotic).
2. **Distributional, not worst-case.** Random 3-SAT at a given α is an *average-case* ensemble. Hardness or easiness here does not place the worst-case decision problem in P or outside P (barrier: average vs worst case; practice vs P).
3. **No universal α* proved here.** A dip in sat. rate or peak in effort near α≈4 is a *reproducible observation* under our parameters. It does not prove a sharp threshold theorem, nor identify a constant that separates complexity classes.
4. **Solver runtime ≠ complexity class.** Even if a solver were fast on all tested samples, hidden exponents, timeouts, and untested adversarial families remain (barriers: hidden constants; small-n illusion).
5. **Evidence ceiling.** Under laboratory policy this report is at most **E2**. Resolving P vs NP would require Category E gates including E5 Lean verification and independent expert review — which this experiment does not attempt.

## Reproducibility command

```bash
python -m backend.experiments.run --problem 3sat --generator random-k-sat --variables 15 --experiment phase-transition --seed 12345 --instances 20
```

## References motivating the search region (not proved by us)

- Mitchell, D., Selman, B., & Levesque, H. (1992). Hard and easy distributions of SAT problems. AAAI.
- Friedgut, E. (1999). Sharp thresholds of graph properties, and the k-sat problem. J. Amer. Math. Soc.
- Achlioptas, D., & Moore, C. (various). Threshold surveys for random k-SAT.
- Mézard, M., Parisi, G., & Zecchina, R. (2002). Analytic and algorithmic solution of random satisfiability problems. Science.

## Methodological alerts

- Negative / messy outcomes (timeouts, disagreements) are retained in the CSV.
- Curve fitting to claim polynomial runtime is **disabled by policy**.
- AI-generated narrative in tooling must be audited (safety rule #13).
