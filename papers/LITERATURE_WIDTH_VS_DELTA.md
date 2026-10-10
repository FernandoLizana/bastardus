# Literature notes (Width vs Δ, Tseitin, outerplanar)

## Classical background

1. **Tseitin (1968)** — unsatisfiable systems of parity constraints on graphs;
   foundational for proof complexity of resolution.
2. **Ben-Sasson & Wigderson (2001)** — width vs size trade-offs for resolution;
   width lower bounds imply size lower bounds.
3. **Atserias / Dalmau** — resolution width and CSP / pebbling-style views.
4. **Urquhart, Bonet–Buss, etc.** — Tseitin formulas as hard examples;
   expansion of the underlying graph controls hardness.
5. **Treewidth characterizations (recent):**
   - Galesi–Itsykson–Riazanov–Sofronova and follow-ups: resolution width of
     Tseitin relates to treewidth / branch-width of G.
   - de Colnet–Mengel (JAIR 2021): regular-resolution *size* of bounded-degree
     Tseitin is polynomial iff tw(G) = O(log n); size ≥ 2^{Ω(tw/Δ)}/n.
   - Itsykson–Riazanov–Sagunov–Smirnov (SAT 2022): tight 2^{Ω(tw)} regular-resolution
     size for all connected G.

## What our lab adds (local, not P vs NP)

These classical results address **asymptotic size** via treewidth. Our line is
**exact equality Width = Δ** on sparse Δ≤3 graphs and a **geometric boundary**:

- Exact **Width = Δ** for trees / cycles / unicyclic (constructive certificates).
- Structured **Width = Δ** for bicyclic Δ≤3 and noncrossing C_n+2 chords via
  path-fold certificates (not only Δ-saturation).
- **Cyclomatic boundary:** γ≤2 ⇒ Width=Δ (in our regime); γ≥3 can exceed.
- Clean law on **C_n + 2 chords:** crossing ⇔ Width>Δ (outerplanar dichotomy).
- Conjecture **C-OUTERPLANAR-WIDTH-EQ-DELTA** (E2-supported on ear families).
- K₄ width-4 witness + path-fold residual + projection-inclusion experiments.

## Novelty vs classical (honest)

| Classical | This lab |
|-----------|----------|
| Lower bounds Size ≥ 2^{Ω(tw)} | Exact Width = Δ for Δ≤3 sparse /
| Hard when tw large / expanders | Soft exact upper bounds = Δ when outerplanar / γ≤2 |
| Rarely pin Width to Δ | Geometric crossing law at Width vs Δ |

Outerplanar graphs have treewidth ≤2, so classical upper bounds already suggest
*small* proof size / width; pinning **Width exactly Δ** and the **crossing
threshold** for γ=3 C_n+2 is the local contribution. We do **not** improve
asymptotic expander lower bounds.

## Not claimed

Any resolution of P vs NP, or lower bounds for general Boolean circuits.
