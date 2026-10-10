"""Shared enums and answer records for the claim gate."""

from __future__ import annotations

from enum import Enum

from pydantic import BaseModel, Field


class CheckStatus(str, Enum):
    UNANSWERED = "unanswered"
    PASS = "pass"
    FAIL = "fail"
    NA = "not_applicable"  # requires justification


class ChecklistAnswer(BaseModel):
    item_id: str
    status: CheckStatus = CheckStatus.UNANSWERED
    justification: str = ""
    artifact_refs: list[str] = Field(default_factory=list)
