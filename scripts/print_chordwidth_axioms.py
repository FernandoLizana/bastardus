#!/usr/bin/env python3
"""Print #print axioms for central ChordWidth theorems (post-build audit)."""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"

THEOREMS = [
    "PNPLab.ChordWidth.k4_hasTreeDecomp_three",
    "PNPLab.ChordWidth.width_from_treewidth_of_characterization",
    "PNPLab.ChordWidth.crossing_width_eq_four",
    "PNPLab.ChordWidth.noncrossing_width_eq_three",
    "PNPLab.ChordWidth.cycle_two_chords_resolution_width_conditional",
    "PNPLab.ChordWidth.BaseCaseTwoChords.TwoChordDiagramLink",
]

SNIPPET = "\n".join(f"#print axioms {name}" for name in THEOREMS)

LEAN_FILE = LEAN / ".tmp_axiom_audit.lean"

MAIN = r"""
import PNPLab.ChordWidth.Main
"""


def main() -> int:
    LEAN_FILE.write_text(MAIN + "\n" + SNIPPET + "\n", encoding="utf-8")
    cmd = ["lake", "env", "lean", str(LEAN_FILE)]
    proc = subprocess.run(cmd, cwd=LEAN, capture_output=True, text=True)
    out = proc.stdout + proc.stderr
    report = ROOT / "reports" / "CHORDWIDTH_AXIOM_AUDIT.md"
    report.write_text(
        "# ChordWidth axiom audit (`#print axioms`)\n\n"
        f"Command: `{' '.join(cmd)}`\n\n"
        "```\n" + out + "\n```\n",
        encoding="utf-8",
    )
    print(out)
    LEAN_FILE.unlink(missing_ok=True)
    return proc.returncode


if __name__ == "__main__":
    raise SystemExit(main())
