/-
  k = 2 link specification: `ChordDiagram n 2` ↔ `CycleTwoChordGraph` (conditional).
-/

import PNPLab.ChordWidth.IntersectionGraph
import PNPLab.ChordWidth.BaseCaseTwoChords.CycleTwoChords

namespace PNPLab.ChordWidth

namespace BaseCaseTwoChords

/--
  **Especificación condicional** (hipótesis explícitas, sin circularidad):

  Un diagrama de 2 acordes refleja `CycleTwoChordGraph g` cuando los endpoints
  coinciden y el cruce en C_n equivale a `g.chordsCross`.
-/
structure TwoChordDiagramLink (g : CycleTwoChordGraph) (D : ChordDiagram g.n 2) : Prop where
  chord0_fst : (D.chords 0).u.val = g.chord1.1
  chord0_snd : (D.chords 0).v.val = g.chord1.2
  chord1_fst : (D.chords 1).u.val = g.chord2.1
  chord1_snd : (D.chords 1).v.val = g.chord2.2
  crossing_iff :
    chordsCrossOnCycle g.n (D.chords 0) (D.chords 1) ↔ g.chordsCross

def twoChordLinkDoc : String :=
  "TwoChordDiagramLink: k=2 coincide con CycleTwoChordGraph bajo hipótesis no degeneradas."

end BaseCaseTwoChords

end PNPLab.ChordWidth
