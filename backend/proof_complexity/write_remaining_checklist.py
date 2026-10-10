"""Sync papers/REMAINING_CHECKLIST.md from code (optional helper)."""

from pathlib import Path

CHECKLIST = Path("papers/REMAINING_CHECKLIST.md").read_text(encoding="utf-8")

if __name__ == "__main__":
    print(CHECKLIST[:500])
    print("...")
