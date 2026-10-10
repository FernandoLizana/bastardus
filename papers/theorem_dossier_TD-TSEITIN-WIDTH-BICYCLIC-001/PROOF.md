# Theorem dossier TD-TSEITIN-WIDTH-BICYCLIC-001

**Statement (working):** For connected bicyclic `G` (`|E|=|V|+1`) with odd charge
`c` and `Δ(G) ≤ 3`, `Width(T(G,c)) = Δ(G)`.

**Status:** Strong E2/E3 evidence + partial constructive structure.

| Layer | Evidence |
|-------|----------|
| Mass checks | 31k+ unit + 20k all-odd, **0** W>Δ |
| General certificate | peel + width-Δ saturation — `prove_bicyclic_lemma` |
| Structured case | `C_n` + **length-2 chord**: ear clip + residual finish — `prove_bicyclic_len2_chord_lemma` |

**Algorithm (general certificate):**

1. Peel degree-1 vertices (Unit–XOR).
2. Saturate resolvents of width ≤ Δ on the 2-core.
3. Verify with `verify_resolution_derivation`.

**Structured subcase:** when the 2-core is a cycle plus a circular-length-2 chord,
clip the triangle ear(s) by deriving residual XOR targets, then finish with
width-2 (cycle) or width-Δ sat on a tree residual (`n=4`).

**Open:** inductive proof for arbitrary chord length / arbitrary bicyclic shape
without saturation search; Lean (E5).

**Camino A/B:** blocked for P vs NP (resolution-only).

**Code:** `backend/proof_complexity/constructive_proofs.py`
