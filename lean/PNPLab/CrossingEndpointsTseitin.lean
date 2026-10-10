/-
  Parametric Tseitin axioms from `CrossingEndpoints` (Category C / G5 track 1).

  Matches Python `_all_axioms` on C_n + two crossing chords with
  `_odd_charge_for_crossing` (charge on sorted endpoint `p0` when Δ ≤ 3).
-/

import PNPLab.CrossingEndpointsGraph
import PNPLab.XorCnf
import PNPLab.OneFoldProjection
import PNPLab.Alt1FoldProjection

namespace PNPLab.Bicyclic

open PNPLab.Resolution

def sortUniqueNat (xs : List Nat) : List Nat :=
  xs.eraseDups.mergeSort (fun a b => decide (a < b))

/-- Cycle neighbors plus crossing-chord neighbors, sorted unique. -/
def CrossingEndpoints.neighbors (e : CrossingEndpoints) (v : Nat) : List Nat :=
  if v < e.n then
    let left := (v + e.n - 1) % e.n
    let right := (v + 1) % e.n
    let chordNbrs :=
      if v = e.p0 then [e.p2]
      else if v = e.p2 then [e.p0]
      else if v = e.p1 then [e.p3]
      else if v = e.p3 then [e.p1]
      else []
    sortUniqueNat (left :: right :: chordNbrs)
  else
    []

/-- Incident edge variables via `edgeVar` (Python `e_index[sorted(v,u)]`). -/
def CrossingEndpoints.incidentVars (e : CrossingEndpoints) (v : Nat) : List Lit :=
  (e.neighbors v).filterMap fun u => e.edgeVar v u

/-- Odd charge on `p0` only (Python `_odd_charge_for_crossing` for Δ ≤ 3). -/
def CrossingEndpoints.oddCharge (e : CrossingEndpoints) (v : Nat) : Nat :=
  if v = e.p0 then 1 else 0

def CrossingEndpoints.xorClausesForVertex (e : CrossingEndpoints) (v : Nat) : List Clause :=
  xorCnfNorm (e.incidentVars v) (e.oddCharge v)

def clauseSortLt (a b : Clause) : Bool :=
  a.length < b.length ||
    (decide (a.length = b.length) && decide (a < b))

def sortClauses (cs : List Clause) : List Clause :=
  cs.mergeSort clauseSortLt

def dedupSortedClauses : List Clause → List Clause
  | [] => []
  | [c] => [c]
  | c :: c' :: rest =>
    if c = c' then dedupSortedClauses (c' :: rest) else c :: dedupSortedClauses (c' :: rest)

/--
  Tseitin axioms for C_n + crossing chords: deduped XOR constraints at each vertex,
  sorted by `(len, clause)` as in Python emit scripts.
-/
def CrossingEndpoints.tseitinAxioms (e : CrossingEndpoints) : List Clause :=
  let raw := (List.range e.n).flatMap (e.xorClausesForVertex ·)
  dedupSortedClauses (sortClauses raw)

theorem c5Ofold_tseitinAxioms_eq_ofold :
    c5OfoldEndpoints.tseitinAxioms = ofoldGAxioms := by
  native_decide

theorem c5Alt1_tseitinAxioms_eq_alt1 :
    c5Alt1Endpoints.tseitinAxioms = alt1GAxioms := by
  native_decide

theorem c5Ofold_tseitinAxioms_length :
    c5OfoldEndpoints.tseitinAxioms.length = 18 := by
  native_decide

theorem c5Alt1_tseitinAxioms_length :
    c5Alt1Endpoints.tseitinAxioms.length = 18 := by
  native_decide

theorem c5Ofold_tseitinAxioms_no_empty :
    ¬ c5OfoldEndpoints.tseitinAxioms.contains [] := by
  native_decide

theorem c5Alt1_tseitinAxioms_no_empty :
    ¬ c5Alt1Endpoints.tseitinAxioms.contains [] := by
  native_decide

theorem c6Endpoints0123_tseitinAxioms_no_empty :
    ¬ c6Endpoints0123.tseitinAxioms.contains [] := by
  native_decide

def crossingEndpointsTseitinDoc : String :=
  "tseitinAxioms from edgeVar/neighbors/oddCharge; matches Python _all_axioms"

def crossingEndpointsTseitinOpenDoc : String :=
  "Closure₃ emitter OK on c5 smokes (CrossingEndpointsClosure3); " ++
  "open: Closure₃(G_e) ∀e + residual XOR under fold"

end PNPLab.Bicyclic
