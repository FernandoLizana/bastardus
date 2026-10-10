/-
  XOR CNF encoding matching Python `tseitin_family.xor_cnf` + `_norm` filtering.
-/

import PNPLab.Resolution

namespace PNPLab.Resolution

/-- Parity of set bits in `mask` (mod 2), matching Python `bin(mask).count("1") % 2`. -/
def popParity : Nat → Nat
  | 0 => 0
  | mask + 1 => ((mask + 1) % 2 + popParity ((mask + 1) / 2)) % 2

/-- Bit `i` of `mask` (0 or 1). -/
def bitAt (mask i : Nat) : Nat :=
  (mask / Nat.pow 2 i) % 2

/-- One XOR-CNF clause from a bitmask over `literals`. -/
def maskClause (literals : List Lit) (mask : Nat) : Clause :=
  literals.zipIdx.map fun (lit, i) =>
    if bitAt mask i = 0 then lit else -lit

partial def xorCnfGo (literals : List Lit) (charge : Nat) (mask limit : Nat)
    (acc : List Clause) : List Clause :=
  if mask >= limit then
    acc
  else
    let acc' :=
      if popParity mask = charge % 2 then acc else acc ++ [maskClause literals mask]
    xorCnfGo literals charge (mask + 1) limit acc'

/-- CNF encoding of `XOR(literals) = charge (mod 2)` (Python `xor_cnf`). -/
def xorCnf (literals : List Lit) (charge : Nat) : List Clause :=
  xorCnfGo literals charge 0 (Nat.pow 2 literals.length) []

/-- Drop tautologies; normalize survivors (Python `_norm`). -/
def normXorClause (C : Clause) : Option Clause :=
  let n := normClause C
  if isTautology n then none else some n

def xorCnfNorm (literals : List Lit) (charge : Nat) : List Clause :=
  (xorCnf literals charge).filterMap normXorClause

end PNPLab.Resolution
