"""Complexity analysis helpers (intentionally conservative)."""

from __future__ import annotations

WARNING = (
    "Never conclude that an algorithm is polynomial-time from finite curve fits. "
    "Use fits only for descriptive comparison (evidence ≤ E2)."
)


def asymptotic_disclaimer() -> str:
    return WARNING
