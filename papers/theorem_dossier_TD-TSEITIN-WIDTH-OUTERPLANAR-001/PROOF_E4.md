# E4 outline: Outerplanar Δ≤3 ⇒ Width = Δ

## Theorem (Category C)

If `G` is connected outerplanar, `Δ(G)≤3`, and `c` is odd, then
`Width(T(G,c)) = Δ(G)`.

## Proof outline

### Step 0 — Lower bound

Axiom width equals the maximum vertex XOR size ≤Δ, so Width ≥ that width; for
Tseitin on simple graphs this is ≤Δ, and for Δ-regular vertices it meets Δ.
(Coarse: Width ≥ max axiom width ≤ Δ; equality uses matching upper bound.)

### Step 1 — Peel trees

While a degree-1 tip exists, Unit–XOR elimination derives the residual
neighbor equation at width ≤Δ (`build_tree` / peel in pathfold). The 2-core
remains outerplanar, connected (or a single edge conflict), odd charge preserved.

### Step 2 — Ear / shortcut induction on the 2-core

While the residual is not a cycle:

- If a **triangle ear** exists (deg-2 tip with adjacent neighbors), fold it
  (XOR-sum / targeted residual) at width ≤Δ.
- Else, by the outerplanar ear-decomposition theorem, there is an ear whose
  internal vertices have degree 2 and endpoints have degree ≥3 in the residual.
  With `Δ≤3` those endpoints have degree 3; a deg-2 tip adjacent to a deg≥3
  vertex admits a **shortcut fold**.

Each fold reduces `|V|` and preserves outerplanarity, Δ≤3, and odd charge.

**Termination:** eventually a cycle remains (`TERMINATION.md`).

### Step 3 — Cycle finish

Odd-charge cycle has Width = 2 ≤ Δ (width-2 saturation / cycle lemma).

## Certificates

`prove_outerplanar_pathfold_lemma` — 130/130 on ear families / triangle chains.
Broad E2 hunts: 0 counterexamples among checked Δ≤3 outerplanar samples.

## Status

E4 outline + constructive algorithm. Lean scaffold:
`lean/PNPLab/Outerplanar.lean` (`EarExistenceClaim`, fold measure).
Missing for E5: actual graph-theoretic ear-existence and fold preservation.
Not P vs NP.
