"""Canonical P vs NP claim gate — process infrastructure only.

This module NEVER asserts that P=NP or P≠NP. It encodes the laboratory's
minimum approval checklist for *purported* resolutions (Category E).

Default outcome of every fresh dossier: may_present_as_resolution = False.
"""

from __future__ import annotations

from .catalog import (
    APPROVAL_CHECKLIST,
    BARRIER_ITEMS,
    CONSEQUENCE_ITEMS_A,
    CONSEQUENCE_ITEMS_B,
    ERROR_DISCARDS,
    NPC_FAMILIES,
    PROBLEM_MODES,
    ClaimSide,
)
from .evaluate import ClaimDossier, GateReport, empty_dossier_template, evaluate_gate
from .schema import CheckStatus, ChecklistAnswer

__all__ = [
    "APPROVAL_CHECKLIST",
    "BARRIER_ITEMS",
    "CONSEQUENCE_ITEMS_A",
    "CONSEQUENCE_ITEMS_B",
    "ERROR_DISCARDS",
    "NPC_FAMILIES",
    "PROBLEM_MODES",
    "CheckStatus",
    "ChecklistAnswer",
    "ClaimDossier",
    "ClaimSide",
    "GateReport",
    "empty_dossier_template",
    "evaluate_gate",
]
