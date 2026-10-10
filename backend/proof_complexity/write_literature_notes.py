"""Literature pointers for the Width-vs-Δ / γ-boundary line (Category C)."""

from __future__ import annotations

NOTES = """
# Literature notes (Width vs Δ, Tseitin, outerplanar)

## Classical background

1. **Tseitin (1968)** — unsatisfiable systems of parity constraints on graphs;
   foundational for proof complexity of resolution.
2. **Ben-Sasson & Wigderson (2001)** — width vs size trade-offs for resolution;
   width lower bounds imply size lower bounds.
3. **Atserias / Dalmau** — resolution width and constraint satisfaction /
   pebbling-style views.
4. **Urquhart, Bonet–Buss, etc.** — Tseitin formulas as hard examples for
   resolution; expansion of the underlying graph controls hardness.

## What our lab adds (local, not P vs NP)

- Exact **Width = Δ** for trees / cycles / unicyclic (constructive certificates).
- Experimental **Width = Δ** for bicyclic Δ≤3.
- **Cyclomatic boundary:** γ≤2 tends to Width=Δ; γ≥3 can exceed.
- Clean law on **C_n + 2 chords:** crossing ⇔ Width>Δ (outerplanar dichotomy).
- K₄ as canonical Width=4>Δ=3 witness; charge-contraction ingredients for a lift.

## Likely overlaps / to cite carefully

- Outerplanar / series-parallel Tseitin may already be known to have small
  width in the literature on matching covered graphs / planar Tseitin.
- Expanderness ⇒ large resolution width is classical; our sparse Δ≤3 regime
  is the opposite end (upper bounds matching Δ).

## Not claimed

Any resolution of P vs NP, or lower bounds for general Boolean circuits.
"""

if __name__ == "__main__":
    from pathlib import Path

    out = Path("papers/LITERATURE_WIDTH_VS_DELTA.md")
    out.write_text(NOTES.lstrip(), encoding="utf-8")
    print(f"wrote {out}")
