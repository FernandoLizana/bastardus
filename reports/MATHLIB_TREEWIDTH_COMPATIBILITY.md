# Mathlib Treewidth Compatibility

**Pin:** Mathlib `v4.32.0` (`lean/lakefile.toml`)  
**ChordWidth API:** vendored `PNPLab/ChordWidth/TreeDecomp/Basic.lean` (faithful to open PR #38334)

---

## Comparison

| Feature | Mathlib v4.32 | ChordWidth vendored |
|---------|---------------|---------------------|
| `SimpleGraph.lineGraph` | ✅ | re-export `LineGraph.lean` |
| `TreeDecomp` structure | ❌ | ✅ `TreeDecomp/Basic.lean` |
| `HasTreeDecomp G k` | ❌ | ✅ `∃ m t, t.width ≤ k` |
| `SimpleGraph.treeWidth` | ❌ | ❌ (not defined) |
| Width convention | — | `max \|bag\| - 1` |
| Certificates | — | Fin-indexed + `native_decide` for finites |

---

## Imports / conflicts

- No namespace collision: all under `PNPLab.ChordWidth`.
- `SmokeLineGraphCert` / `AsymptoticLineGraphCert` namespaces for generated certs.
- `Treewidth.lean` defines `TreewidthCertificate` as `HasTreeDecomp` wrapper.

---

## Upgrade risks (if bumping Mathlib)

| Risk | Severity |
|------|----------|
| PR #38334 lands with different `width` definition | High |
| Breaking changes in `SimpleGraph.lineGraph` | Medium |
| Full PNPLab build OOM | High (do **not** `lake build PNPLab`) |

**Recommendation:** Keep adapter layer:

```lean
-- Future: translate official treeWidth to HasTreeDecomp
def treewidthAtMost := HasTreeDecomp
```

Do **not** auto-upgrade pin during universal proof work.

---

## Pathwidth alternative

Mathlib may have partial pathwidth elsewhere — not wired in ChordWidth. Route F (path decomposition) can use same `TreeDecomp` with `certPathGraph` (path is a tree).

---

## Status

**BLOCKED BY LIBRARY** for official `SimpleGraph.treeWidth` — **not blocking** universal proof via vendored `HasTreeDecomp`.
