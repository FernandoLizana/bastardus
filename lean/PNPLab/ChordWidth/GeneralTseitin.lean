/-
  General Tseitin encoder (documentation + literature layer).

  Concrete encoders: `BaseCaseTwoChords/TseitinEncoding.lean`, `PNPLab.CrossingEndpointsTseitin`.
-/

import PNPLab.ChordWidth.LiteratureHypothesis

namespace PNPLab.ChordWidth

def generalTseitinDoc : String :=
  "Encoder unificado: CycleTwoChordGraph.tseitinFromMarking / CrossingEndpoints.tseitinAxioms; " ++
  "ver BaseCaseTwoChords/TseitinEncoding.lean."

end PNPLab.ChordWidth
