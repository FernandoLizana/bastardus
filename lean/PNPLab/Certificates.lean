/-
  Finite graph certificates used by the laboratory.

  Software cross-checks live in `backend/reductions/*` (evidence ≤ E2).
  These Lean definitions target E5 for certificate-verification lemmas only,
  not for P vs NP.
-/

namespace PNPLab

structure SimpleGraph where
  n : Nat
  edges : List (Nat × Nat)
  deriving Repr

def edgeMem (G : SimpleGraph) (u v : Nat) : Bool :=
  let p := if u < v then (u, v) else (v, u)
  G.edges.contains p

def listNodup : List Nat → Bool
  | [] => true
  | x :: xs => !(xs.contains x) && listNodup xs

def allInRange (n : Nat) (xs : List Nat) : Bool :=
  xs.all (fun u => decide (u < n))

def isCliqueCert (G : SimpleGraph) (k : Nat) (verts : List Nat) : Bool :=
  decide (verts.length = k) &&
    allInRange G.n verts &&
    listNodup verts &&
    verts.all (fun u =>
      verts.all (fun v =>
        decide (u = v) || edgeMem G u v))

def isVertexCoverCert (G : SimpleGraph) (k : Nat) (verts : List Nat) : Bool :=
  decide (verts.length = k) &&
    allInRange G.n verts &&
    listNodup verts &&
    G.edges.all (fun e => verts.contains e.fst || verts.contains e.snd)

def isIndependentSetCert (G : SimpleGraph) (k : Nat) (verts : List Nat) : Bool :=
  decide (verts.length = k) &&
    allInRange G.n verts &&
    listNodup verts &&
    verts.all (fun u =>
      verts.all (fun v =>
        decide (u = v) || !(edgeMem G u v)))

theorem empty_is_zero_clique (G : SimpleGraph) :
    isCliqueCert G 0 [] = true := by
  simp [isCliqueCert, allInRange, listNodup]

theorem empty_cover_on_edgeless (n : Nat) :
    isVertexCoverCert ⟨n, []⟩ 0 [] = true := by
  simp [isVertexCoverCert, allInRange, listNodup]

theorem empty_is_zero_independent (G : SimpleGraph) :
    isIndependentSetCert G 0 [] = true := by
  simp [isIndependentSetCert, allInRange, listNodup]

def softwareLinkClique : String :=
  "backend/reductions/sat_to_clique.py#three_sat_to_clique"

end PNPLab
