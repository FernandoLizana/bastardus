"""Structural law for Tseitin width on C_n + two chords (Δ≤3).

Empirical theorem (E2, n≤10, unit charge; 783/783):
  The two chords must use four distinct endpoints (Δ≤3).
  Width(T(G,c)) = Δ(G)  ⇔  the chords are non-crossing on the cycle.
  Width(T(G,c)) > Δ(G)  ⇔  the chords cross.

Crossing: endpoints alternate around the cycle
(standard circle-chord crossing).
"""

from __future__ import annotations


def circular_dist(n: int, a: int, b: int) -> int:
    d = abs(a - b) % n
    return min(d, n - d)


def chords_cross_on_cycle(n: int, c1: tuple[int, int], c2: tuple[int, int]) -> bool:
    """True iff the two chords cross when drawn as straight chords of C_n."""
    a, b = c1
    c, d = c2
    if len({a, b, c, d}) < 4:
        raise ValueError("chords must have four distinct endpoints")

    def on_open_arc(p: int, s: int, t: int) -> bool:
        """p lies on the open clockwise arc s → t on Z/nZ."""
        p, s, t = p % n, s % n, t % n
        if s < t:
            return s < p < t
        return p > s or p < t

    return on_open_arc(c, a, b) != on_open_arc(d, a, b)


def predict_width_vs_delta_cycle_two_chords(
    n: int, c1: tuple[int, int], c2: tuple[int, int]
) -> str:
    """Return 'eq' or 'gt' under the crossing law (does not compute width)."""
    return "gt" if chords_cross_on_cycle(n, c1, c2) else "eq"
