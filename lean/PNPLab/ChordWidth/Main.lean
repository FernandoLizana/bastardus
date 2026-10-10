/-
  PNPLab/ChordWidth entry point — P≠NP research program (first delivery).

  **No claim** that current results demonstrate or approach P≠NP.
  Two-chord width 3/4 = finite-structural base case only.
-/

import PNPLab.ChordWidth.LiteratureHypothesis
import PNPLab.ChordWidth.GeneralTseitin
import PNPLab.ChordWidth.LineGraph
import PNPLab.ChordWidth.Treewidth
import PNPLab.ChordWidth.TreeDecomp.CertificatesLine
import PNPLab.ChordWidth.TreeDecomp.CertificatesLineSmokes
import PNPLab.ChordWidth.TreeDecomp.CertificatesAsymptotic
import PNPLab.ChordWidth.ChordDiagram
import PNPLab.ChordWidth.IntersectionGraph
import PNPLab.ChordWidth.TopologicalCore
import PNPLab.ChordWidth.BaseCaseTwoChords.Main

namespace PNPLab.ChordWidth

def researchProgramDoc : String :=
  "Programa ChordWidth → barreras P≠NP. Base finita k=2 (3/4); k-chord general; " ++
  "escaneo tw(I/L/G); familia asintótica candidata. Ver reports/CHORDWIDTH_PNP_RESEARCH_PROGRAM.md"

def fileMapDoc : String :=
  "TreeDecomp/Basic.lean | Treewidth.lean | ChordDiagram.lean | IntersectionGraph.lean | " ++
  "TopologicalCore.lean | GeneralTseitin.lean | BaseCaseTwoChords/* | Main.lean"

def pnpDistanceDoc : String :=
  "Distancia a P≠NP: sin cota inferior superpolinomial formalizada; " ++
  "sin reducción SAT→familia ChordWidth; barrera GCT/relativización intacta."

end PNPLab.ChordWidth
