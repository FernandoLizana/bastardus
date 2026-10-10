# LeanSearch Query Log

**Note:** LeanSearch MCP not invoked in this session; queries recorded for follow-up.

| # | Mathematical query | Lean-oriented query | Purpose | Result |
|---|-------------------|---------------------|---------|--------|
| 1 | treewidth of line graph subdivision | `SimpleGraph.lineGraph` treewidth | Route B | Pending |
| 2 | pathwidth path graph decomposition | `pathGraph` `TreeDecomp` | Route F | `certPathGraph` local |
| 3 | clique minor treewidth lower bound | `TreeDecomp` width clique | Route C | Mathlib partial |
| 4 | outerplanar line graph treewidth | `IsOuterplanar` lineGraph | Route E | Not found v4.32 |

---

## Manual Mathlib inventory (v4.32)

- `SimpleGraph.lineGraph` — available
- `SimpleGraph.pathGraph` — available (used in CertPathGraph)
- `TreeDecomp` — **local vendored only**

---

## Next queries when LeanSearch available

1. "treewidth at least clique size minus one"
2. "series parallel graph treewidth"
3. "edge subdivision line graph"
