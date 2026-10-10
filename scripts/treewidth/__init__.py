"""Small treewidth helpers for verification scripts.

PyPI has no package named ``treewidth``; this module wraps NetworkX
heuristics plus an exact branch-and-bound solver for modest graphs.
"""

from __future__ import annotations

from .compute import compute_treewidth, treewidth_lower_bound

__all__ = ["compute_treewidth", "treewidth_lower_bound"]
