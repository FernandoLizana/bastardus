# Known Barriers

Automated helpers live in `backend/research_barriers/`.
This document expands the scientific content. Checklist reports are **E0/E1 guidance**, not refutations.

## 1. Relativization (Baker–Gill–Solovay, 1975)

There are oracles \(A,B\) with \(\mathbf{P}^A=\mathbf{NP}^A\) and \(\mathbf{P}^B\neq\mathbf{NP}^B\). Relativizing techniques cannot settle P vs NP.

## 2. Natural proofs (Razborov–Rudich, 1997)

Under cryptographic assumptions, large constructive combinatorial properties usable as circuit lower bounds are “too natural” to separate P from NP.

## 3. Algebrization (Aaronson–Wigderson, 2008)

Extends relativization obstruction to many arithmetization-based techniques.

## 4. Limits of diagonalization

Diagonalization alone is compatible with both relativized worlds.

## 5. Restricted vs general lower bounds

AC⁰ / monotone / bounded-depth bounds need lifting theorems to apply to general circuits.

## 6. Average-case vs worst-case

Fast typical instances ≠ language in P.

## 7. Finite vs asymptotic

Finite experiments cannot prove asymptotic statements for all \(n\).

## 8. Practice vs P

Industrial SAT performance is not a complexity classification.

## 9. Hidden constants / exponents

\(n^{100}\) or \(2^{n/100}\) can look gentle at small \(n\).

## 10. Small-\(n\) polynomial illusion

Curve fits on tiny sizes routinely mislead.

## Mandatory questions for any new “proof”

- ¿La propuesta relativiza?
- ¿Parece una natural proof?
- ¿Depende de propiedades verificables y amplias?
- ¿Solo funciona en circuitos restringidos?
- ¿Asume indirectamente lo que demuestra?
- ¿Confunde promedio con peor caso?
- ¿Depende de muestras finitas?
- ¿Hay familia adversarial conocida?
- ¿Se omitió el coste de una subrutina?
- ¿Crecen exponencialmente bits / estructuras internas?
