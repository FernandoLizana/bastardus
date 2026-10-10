"""Resource and search instrumentation for solvers.

WARNING: Finite timing curves never imply asymptotic membership in P
or separation of complexity classes (evidence ≤ E2).
"""

from __future__ import annotations

import sys
import time
import tracemalloc
from collections.abc import Callable, Iterator
from contextlib import contextmanager
from dataclasses import dataclass, field
from typing import TypeVar

import psutil

T = TypeVar("T")


@dataclass
class SolverMetrics:
    """Search and resource metrics collected during a solver run."""

    decisions: int = 0
    backtracks: int = 0
    propagations: int = 0
    conflicts: int = 0
    pure_literal_eliminations: int = 0
    unit_propagations: int = 0
    max_depth: int = 0
    wall_time_seconds: float = 0.0
    cpu_time_seconds: float = 0.0
    peak_memory_bytes: int = 0
    timed_out: bool = False
    solver_name: str = ""
    notes: list[str] = field(default_factory=list)

    def record_decision(self, depth: int) -> None:
        self.decisions += 1
        self.max_depth = max(self.max_depth, depth)

    def record_backtrack(self) -> None:
        self.backtracks += 1

    def to_dict(self) -> dict[str, object]:
        return {
            "decisions": self.decisions,
            "backtracks": self.backtracks,
            "propagations": self.propagations,
            "conflicts": self.conflicts,
            "pure_literal_eliminations": self.pure_literal_eliminations,
            "unit_propagations": self.unit_propagations,
            "max_depth": self.max_depth,
            "wall_time_seconds": self.wall_time_seconds,
            "cpu_time_seconds": self.cpu_time_seconds,
            "peak_memory_bytes": self.peak_memory_bytes,
            "timed_out": self.timed_out,
            "solver_name": self.solver_name,
            "notes": list(self.notes),
        }


def _cpu_time() -> float:
    proc = psutil.Process()
    times = proc.cpu_times()
    return float(times.user + times.system)


@contextmanager
def measure_resources(metrics: SolverMetrics) -> Iterator[None]:
    """Context manager that fills wall/CPU time and peak memory into *metrics*."""
    tracemalloc.start()
    wall0 = time.perf_counter()
    cpu0 = _cpu_time()
    try:
        yield
    finally:
        metrics.wall_time_seconds = time.perf_counter() - wall0
        metrics.cpu_time_seconds = max(0.0, _cpu_time() - cpu0)
        _current, peak = tracemalloc.get_traced_memory()
        tracemalloc.stop()
        # Also consider RSS delta via psutil as a secondary signal
        try:
            rss = psutil.Process().memory_info().rss
            metrics.peak_memory_bytes = max(metrics.peak_memory_bytes, peak, rss)
        except Exception:  # noqa: BLE001
            metrics.peak_memory_bytes = max(metrics.peak_memory_bytes, peak)


def timed_call(fn: Callable[[], T], metrics: SolverMetrics) -> T:
    """Run *fn* while collecting resource metrics."""
    with measure_resources(metrics):
        return fn()
