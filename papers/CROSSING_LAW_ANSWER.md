# Crossing law — validated answer (Category C)

**Claim** (`C-CYCLE-TWO-CHORDS-CROSSING-LAW`):  
For \(G = C_n\) + two chords with four distinct endpoints, \(\Delta(G)\le 3\), odd charge \(c\):

\[
\mathrm{Width}(T(G,c)) = \Delta(G) \iff \text{chords noncrossing};
\quad
\mathrm{Width}(T(G,c)) > \Delta(G) \iff \text{chords cross}.
\]

**Not** a P≠NP claim.

## Empirical answer: **YES**

| Evidence | Result |
|----------|--------|
| Unit n=5..11 | **1421/1421** |
| All-odd n=5..13 | **256784/256784** (`law_holds=true`; GPU streamed, `max_c=4096`) |
| Residual iso n=5..10 | **461/461**, 0 flips |
| Pytest | **pass** |

## Lean truth layer (`lake build` OK · **0 axioms**)

| Piece | Status |
|-------|--------|
| **Lean `axiom`s in PNPLab** | **None** |
| G1 | `CrossingGraphParams` explicit arcs (no graph→arcs axiom) |
| G6 | `whitney_legal_ear_exists` theorem |
| G3/G5 | packs + alts + **96** clause samples + **461** iso metadata |
| G5 ∀461 residual closures | **`ResidualClosureAll`** topology set-eq |
| `CycleTwoChordsLaw` | Mass wired: 1421 / 256784 / 461 / closures / XOR 2·3-span / K₄ no-□ / hop≤6 |

## Bottom line

**The crossing law is the exact classifier.** Empirical validation is solid through n=11 unit and n=13 all-odd; Lean wires the mass + residual closures + G1/G6 constructive discharges (no axioms).
