"""SAT and combinatorial solvers.

All solvers report SolverResult with explicit evidence tagging.
Empirical speed never implies membership in P.
"""

from backend.solvers.base import SolverResult
from backend.solvers.brute_force import BruteForceSAT
from backend.solvers.dpll import BranchingHeuristic, DPLLSolver
from backend.solvers.meta import MetaSolver, extract_features
from backend.solvers.pysat_adapter import PySATSolver

__all__ = [
    "BranchingHeuristic",
    "BruteForceSAT",
    "DPLLSolver",
    "MetaSolver",
    "PySATSolver",
    "SolverResult",
    "extract_features",
]
