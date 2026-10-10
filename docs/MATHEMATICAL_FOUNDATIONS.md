# Mathematical Foundations

**Status:** Documentation of *standard* definitions with citations.
**Evidence for definitions:** known textbook results (not novel).
**This file does not resolve P vs NP.**

## Central question

Is \(\mathbf{P} = \mathbf{NP}\)?

We use standard definitions from:

1. Arora, S., & Barak, B. (2009). *Computational Complexity: A Modern Approach*. Cambridge University Press.
2. Sipser, M. (2012). *Introduction to the Theory of Computation* (3rd ed.). Cengage.
3. Garey, M. R., & Johnson, D. S. (1979). *Computers and Intractability*. W. H. Freeman.
4. Cook, S. A. (1971). The complexity of theorem-proving procedures. STOC.
5. Karp, R. M. (1972). Reducibility among combinatorial problems. In *Complexity of Computer Computations*.

## Deterministic Turing machine (DTM)

A deterministic Turing machine is a tuple
\((Q, \Sigma, \Gamma, \delta, q_0, q_{\mathrm{accept}}, q_{\mathrm{reject}})\)
with transition function \(\delta: Q \setminus \{q_{\mathrm{accept}}, q_{\mathrm{reject}}\} \times \Gamma \to Q \times \Gamma \times \{L,R\}\)
(standard multi-tape variants are allowed; see Arora–Barak Ch. 1).

## Nondeterministic Turing machine (NTM)

As a DTM, except \(\delta\) maps to a *set* of possible transitions (Sipser; Arora–Barak).
An NTM accepts iff *some* computation branch accepts.

## Language

A language \(L \subseteq \{0,1\}^*\) is a set of finite binary strings (or over a finite alphabet, via encoding).

## Time and space complexity

- A DTM runs in time \(T(n)\) if on every input of length \(n\) it halts within \(T(n)\) steps.
- Space \(S(n)\) is the number of work-tape cells used.
- \(\mathrm{TIME}(T(n))\), \(\mathrm{SPACE}(S(n))\) as usual (Arora–Barak Ch. 1–4).

## Class P

\[
\mathbf{P} = \bigcup_{c \ge 1} \mathrm{TIME}(n^c)
\]
languages decided by a DTM in worst-case polynomial time.

## Verifiable certificates & class NP

A language \(L\) is in \(\mathbf{NP}\) if there exists a polynomial \(p\) and a polynomial-time DTM \(V\) (verifier) such that
\[
x \in L \iff \exists u \in \{0,1\}^{p(|x|)}:\ V(x,u)=1.
\]
Equivalently, \(L\) is decided by a polynomial-time NTM (Sipser; Arora–Barak Ch. 2).

## Polynomial-time (Karp) reduction

\(A \le_p B\) if there is a polynomial-time computable \(f\) with \(x \in A \iff f(x) \in B\).

## NP-hard / NP-complete

- \(B\) is **NP-hard** if every \(A \in \mathbf{NP}\) satisfies \(A \le_p B\).
- \(B\) is **NP-complete** if \(B \in \mathbf{NP}\) and \(B\) is NP-hard.

## SAT / 3-SAT

- **SAT:** given a Boolean formula (here: CNF), does there exist a satisfying assignment?
- **3-SAT:** SAT restricted to 3-CNF (each clause width 3).

SAT is NP-complete (Cook 1971; Levin). 3-SAT is NP-complete via a standard poly-time reduction from SAT (Karp; textbooks).

## Cook–Levin theorem

SAT is NP-complete: every language in NP poly-time reduces to SAT (Cook 1971; Levin independently). Proof idea: tableau / computation trace encoded as local constraints (Arora–Barak Ch. 2).

## Uniformity

Uniform complexity classes (P, NP, …) are defined via Turing machines computing one algorithm for all input lengths. Non-uniform classes (e.g. \(\mathbf{P}/\mathrm{poly}\)) allow advice strings per length (Arora–Barak Ch. 6).

## Worst-case vs average-case

Membership in \(\mathbf{P}\) is a *worst-case* statement. Average-case complexity (distributions over instances) is a distinct theory; heuristic success on random 3-SAT does not imply \(\mathrm{SAT} \in \mathbf{P}\).

## Pseudo-polynomial algorithms

Runtime polynomial in *numeric magnitudes* but exponential in *bit length* (classic Knapsack DP). Not polynomial-time in the Turing machine sense.

## Parameterized algorithms

FPT: time \(f(k) \cdot n^{O(1)}\) for parameter \(k\) (Downey & Fellows; Cygan et al.). FPT ≠ poly-time unless the parameter is \(O(1)\) or specially bounded.

## Boolean circuits & circuit lower bounds

Families \(\{C_n\}\) of Boolean circuits; size/depth measures. Proving super-polynomial circuit lower bounds for NP is a major route toward \(\mathbf{P} \ne \mathbf{NP}\), obstructed in part by natural proofs (Razborov–Rudich 1997).

## Implementation mapping

| Concept | Code |
|---------|------|
| CNF / 3-CNF | `backend/models/cnf.py` |
| Certificate check | `verify_assignment` |
| 3-SAT → Clique | `backend/reductions/sat_to_clique.py` |

## 3-SAT → Clique (Karp) — correctness sketch

**Known result** (not claimed novel). Vertices = literal occurrences; edges join non-conflicting literals in distinct clauses; ask for clique of size \(m\) (#clauses). Satisfying assignments ↔ \(m\)-cliques. Empirical validation in tests is **E2**; Lean proof is future work.
