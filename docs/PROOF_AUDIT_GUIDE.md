# Proof Audit Guide

Module: `backend/proof_auditor`

## Input

Markdown or LaTeX **text** (file or API body) claiming a complexity result.

## Output structure

- Affirmation analyzed
- Assumptions
- Steps that appear locally valid
- Doubtful steps
- Critical step
- Potential counterexample / stress test
- Relevant barriers
- Evidence level of the **audit** (typically E1)
- Provisional conclusion

## What it detects (heuristics)

Circular reasoning cues, bad quantifier patterns, universal claims from examples,
heuristic-as-always, wrong reduction direction, pseudo-polynomial as polynomial,
exponential preprocessing, NP vs NPC confusion, restricted-case generalization,
average-as-worst-case language, etc.

## What it does **not** do

- Verify formal proofs
- Certify correctness if no flags fire
- Replace Lean or human referees

**Never declare a proof correct solely because an LLM or this auditor found no errors.**
