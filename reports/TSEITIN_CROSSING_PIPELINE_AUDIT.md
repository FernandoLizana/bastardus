# Tseitin Crossing Pipeline Audit

**File:** `lean/PNPLab/ChordWidth/BaseCaseTwoChords/TseitinEncoding.lean`  
**External:** `PNPLab/CrossingEndpointsTseitin.lean`

---

## Architecture

| Branch | Encoder | Parametric on `CycleTwoChordGraph`? |
|--------|---------|-------------------------------------|
| Noncrossing | `tseitinAxiomsNoncrossingFromMarking` | **Yes** (chord1/chord2 endpoints) |
| Crossing | `toCrossingEndpoints` → `CrossingEndpoints.tseitinAxioms` | **Partial** (requires `chordsCross`, uses fixed CrossingEndpoints API) |

---

## Crossing path (current)

```lean
def CycleTwoChordGraph.tseitinAxiomsFromMarking ... :=
  match pairing with
  | .crossing => (g.toCrossingEndpoints hc).tseitinAxioms
  | _ => g.tseitinAxiomsNoncrossingFromMarking φ

theorem tseitinAxioms_crossing_eq :
  g.tseitinAxioms_crossing hc = (g.toCrossingEndpoints hc).tseitinAxioms
```

**Assessment:** Crossing is parametric **in endpoint order** via `CrossingEndpoints`, but **not** unified in the same `edgeList/neighbors/incidentVars` pipeline as noncrossing.

---

## Variables and φ

- **defaultOddMarking:** charge 1 at `p0`, 0 elsewhere — odd total charge.
- **Noncrossing:** parity constraints per vertex via `neighbors` + `incidentVars`.
- **Crossing:** delegated to `CrossingEndpointsTseitin` (separate edge variable numbering).

---

## Connection to width

`TwoChordWidthContext` requires:

```lean
char : TseitinWidthTreewidthCharacterization (Fin g.n) g.toSimpleGraph 3 k
```

This **assumes** Galesi width identity — not derived from encoder.

Smoke wiring (`TwoChordSmokeTseitinUnification`) connects fixed instances only.

---

## G5 status

| Criterion | Met? |
|-----------|------|
| Encoder crossing parametric | **Partial** (via CrossingEndpoints bridge) |
| All valid crossing instances | **Not audited end-to-end** |
| Correctness formalized | **OPEN** (equivalence to abstract Tseitin) |
| Connected without smoke-only | **OPEN** |
| Symmetric with noncrossing | **No** |

**Classification:** **OPEN** (not closed)

---

## Recommended work

1. Prove `CrossingEndpoints.tseitinAxioms` equals generic encoder on `toSimpleGraph` for all crossing `g`.
2. Unify edge indexing (`edgeVar`) across branches.
3. Parameterize `crossingTseitinEncoding (g) (hc) (φ)` with correctness lemma.
4. Only then wire `TwoChordWidthContext` without smoke unification.

---

## Conditional result allowed now

```text
Given TseitinWidthTreewidthCharacterization + HasTreeDecomp tw=4
→ ResolutionWidth = 4
```

Already present as conditional theorems in Laws — **CONDITIONAL**, not G5 closure.
