# ChordWidth Formal Problem Statement

**Status:** specification document (not a Lean proof)

---

## 1. Graph family

### 1.1 Cycle base

- **C_n:** simple cycle on vertices `{0,…,n−1}` with edges `(i, (i+1) mod n)`.
- **Minimum n:** Lean requires `p0 < p1 < p2 < p3 < n` ⇒ **n ≥ 4** structurally; meaningful two-chord instances typically **n ≥ 5**.

### 1.2 Representation (`CycleTwoChordGraph`)

```lean
structure CycleTwoChordGraph where
  n : Nat
  p0 p1 p2 p3 : Nat
  pairing : ChordPairing  -- crossing | nested | disjoint
  ordered : p0 < p1 ∧ p1 < p2 ∧ p2 < p3 ∧ p3 < n
```

### 1.3 Chords

| Pairing | chord1 | chord2 |
|---------|--------|--------|
| crossing | (p0, p2) | (p1, p3) |
| nested | (p0, p3) | (p1, p2) |
| disjoint | (p0, p1) | (p2, p3) |

### 1.4 Crossing vs noncrossing

- **Crossing:** `pairing = crossing` (`chordsCross`).
- **Noncrossing:** `pairing ∈ {nested, disjoint}`.

Python also uses geometric `chords_cross_on_cycle` for validation; aligned for gap-pattern enumeration.

---

## 2. Validity filters

| Predicate | Meaning |
|-----------|---------|
| `endpointsDistinct` | PROVED from `ordered` |
| `isNondegenerate` | neither chord is already a cycle edge |
| `realMaxDegreeThree` / `isDelta3Admissible` | `maxDegree(toSimpleGraph) = 3` |
| `isFullyDegenerate` | both chords on cycle edges ⇒ Δ=2 |

**Python Δ=3 filter:** skip configs with `max(degree) ≠ 3`.

**Lean gap:** generic `realMaxDegreeThree` only proved for crossing and nested nondegenerate; not all disjoint/noncrossing without `isNondegenerate`.

**Degenerate cases to exclude from G1:** chord = cycle edge; duplicate endpoints (excluded by ordered strict); Δ ≠ 3.

---

## 3. Line graph

- **Mathlib:** `SimpleGraph.lineGraph G` on edge set of `G`.
- **Certificates:** Fin-indexed reindexing of edges to `Fin |E(G)|` for decidable proofs.

---

## 4. Treewidth convention (repo)

From `TreeDecomp/Basic.lean`:

```lean
def width (t : TreeDecomp G m) : Nat :=
  (Finset.univ : Finset (Fin m)).sup fun w => (t.bag w).card - 1

def HasTreeDecomp (G : SimpleGraph V) (k : Nat) : Prop :=
  ∃ m t, t.width ≤ k
```

**Bag size vs width:** width = max \|bag\| − 1.

---

## 5. Target theorems (mathematical)

### G1a (noncrossing upper)

∀ valid G with ¬crossing: `tw(L(G)) ≤ 3`.

### G1b (noncrossing lower)

∀ valid G with ¬crossing: `3 ≤ tw(L(G))`.

### G1c (crossing upper/lower)

∀ valid G with crossing: `tw(L(G)) = 4`.

### Combined G1

`tw(L(G)) = 3` iff noncrossing; `= 4` iff crossing (under validity).

---

## 6. Tseitin / resolution width

**Literature (Galesi et al., conditional in Lean):**

```text
Width(T(G,φ)) = max(Δ(G), tw(L(G)))   [hypotheses: connected G, unsat odd marking, ...]
```

**Lean:** `TseitinWidthTreewidthCharacterization` packages `tseitin` + `width_eq` as **assumed** field.

**φ:** odd marking on edges; default smoke `defaultOddMarking` charges p0.

**Crossing encoder:** reduces to `CrossingEndpoints` when `chordsCross`.

**Noncrossing encoder:** `tseitinAxiomsNoncrossingFromMarking`.

---

## 7. Lean target signatures (skeletons — not in compilable sorry form)

```lean
-- Upper bound pilot (OPEN):
theorem lineGraph_hasTreeDecomp_three_of_noncrossing
    (g : CycleTwoChordGraph) (hΔ : g.isDelta3Admissible) (hnc : ¬ g.chordsCross) :
    HasTreeDecomp (SimpleGraph.lineGraph g.toSimpleGraph) 3

-- Universal equality (OPEN):
theorem lineGraph_treeWidth_eq_three_of_noncrossing ... := ...
theorem lineGraph_treeWidth_eq_four_of_crossing ... := ...
```

Use `HasTreeDecomp` until Mathlib `treeWidth` merges.

---

## 8. Classification of current evidence

| Claim | Status |
|-------|--------|
| tw dichotomy n≤14 exact | COMPUTATIONALLY VERIFIED |
| tw dichotomy ∀n | OPEN |
| Width=3/4 from tw | CONDITIONAL (Galesi structure) |
| Core K4/C4 ∀n | OPEN |
