# Research Methodology

## Evidence taxonomy

Every claim in logs, APIs, and reports must carry:

- `evidence_level` ∈ {E0,…,E6}
- `claim_type` ∈ {
  `observation_experimental`, `conjecture`, `lemma`, `partial_proof`,
  `formal_proof`, `known_result`, `apparently_new`, `error_or_inconclusive`
  }

### Hard rule

**The software must never present anything below E5 as a resolution of P vs NP.**
Additionally, Category-E resolution candidates must pass the canonical checklist in
[`docs/P_VS_NP_CLAIM_GATE.md`](P_VS_NP_CLAIM_GATE.md) (Camino A or B, families, modes,
error discards, barriers, consequences, approval items) via `backend.claim_gate`.

## Scientific safety rules

1. Do not invent references.
2. Do not invent theorems.
3. Do not declare novelty without literature search.
4. Absence of counterexamples ≠ proof.
5. Do not hide negative experiments.
6. Do not cherry-pick favorable results.
7. Record hypothesis changes after seeing data (pre-registration culture).
8. Record seeds and parameters.
9. Keep datasets immutable (content-hash).
10. Separate exploration, training, and validation.
11. Audit AI-suggested mathematics.
12. Require independent verification for critical claims.
13. Label AI-generated text clearly.
14. Do not submit purported P vs NP solutions to CMI without professional review.

## Result categories

- **A** Engineering
- **B** Experimental
- **C** Restricted theory
- **D** Significant theory
- **E** P vs NP–related candidate — only with full formulation, adversarial review, substantial formalization, literature comparison, and independent experts.

Favor realistic C/D outcomes over promising E.

## Adversarial dual agents (process)

- **Proposer:** patterns, lemmas, algorithms, invariants, proof sketches.
- **Refuter:** counterexamples, quantifiers, hidden costs, barriers, reduction breaks.

No hypothesis advances without a Refuter report (barrier checklist minimum).

## Proposal template

Use for mathematical ideas:

## Propuesta
## Definiciones
## Afirmación exacta
## Por qué podría ser útil
## Evidencia disponible
## Intento de demostración
## Intento de refutación
## Contraejemplos buscados
## Barreras aplicables
## Coste computacional real
## Resultado conocido más cercano
## Nivel de evidencia
## Próximo experimento
