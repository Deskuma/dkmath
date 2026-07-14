
# Codex instructions

Target:
DkMath.Analysis.DkReal.SemanticCF2DPhaseShift

Goal:
Continue checkpoint 104 by preparing the cyclic-index layer for shifted normalized paths. The shifted normalized edge is already continuous and packaged both as a `Vec Real` path and as a fixed-`q2` level-set path. Now expose indexed shifted edges using iterated semantic actions and prove adjacent seam compatibility in indexed form. Do not introduce Euclidean angle language yet.

Principle:
Keep this layer pre-geometric. Do not use angle, arc, degree, circle, rotation, piOverFour, or fortyFive in Lean theorem names. The goal is cyclic indexing, endpoint compatibility, and four-edge concatenation readiness on the fixed `q2` boundary.

Context:
`shiftedSemanticNormalizedEdge` is implemented. It preserves `q2`, starts at the left normalized center candidate, ends at the right normalized center candidate, reaches `semanticAct r z` at `phaseCenter`, is continuous, and is packaged as `shiftedSemanticNormalizedPath` and `shiftedSemanticNormalizedLevelPath`.

Part A:
Add indexed starting states for shifted edges.

Prefer reusing the existing `semanticActIter` API if available in the imported context. If it is not imported, either import the module that exposes it or define a local wrapper only if appropriate.

Candidate definition:

```lean id="co8xrt"
def shiftedSemanticIndexedBase
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) : Vec ℝ :=
  semanticActIter r k z
```

If `semanticActIter` is unavailable or would create import trouble, use `(semanticAct r)^[k] z` directly.

Part B:
Define indexed shifted normalized edges and paths.

Candidate definitions:

```lean id="okty33"
def shiftedSemanticIndexedEdge
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) (t : ℝ) : Vec ℝ :=
  shiftedSemanticNormalizedEdge r (shiftedSemanticIndexedBase r z k) t

def shiftedSemanticIndexedPath
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) :
    Path
      (shiftedSemanticLeftEndpoint r (shiftedSemanticIndexedBase r z k))
      (shiftedSemanticRightEndpoint r (shiftedSemanticIndexedBase r z k)) :=
  shiftedSemanticNormalizedPath r (shiftedSemanticIndexedBase r z k)
```

For the fixed `q2` level-set version, only add it if the endpoint type is not too cumbersome. If it becomes noisy, leave a TODO and keep the `Vec Real` path version.

Part C:
Prove indexed adjacent seam compatibility.

Candidate theorem:

```lean id="dhm09f"
theorem shiftedSemanticIndexedEdge_right_eq_next_left
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (k : ℕ) :
    shiftedSemanticIndexedEdge r z k 1 =
      shiftedSemanticIndexedEdge r z (k + 1) 0
```

Expected route:
Unfold indexed definitions and use `shiftedSemanticNormalizedEdge_right_eq_next_left`. If the base uses `semanticActIter`, use the succ theorem for `semanticActIter`.

Part D:
Prove indexed center-to-next-action compatibility under core-zero.

Candidate theorem:

```lean id="s8lwkt"
theorem shiftedSemanticIndexedEdge_center_eq_next_base_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (k : ℕ) :
    shiftedSemanticIndexedEdge r z k phaseCenter =
      shiftedSemanticIndexedBase r z (k + 1)
```

Expected route:
Use `shiftedSemanticNormalizedEdge_center_eq_semanticAct_of_core_eq_zero` at the indexed base and the succ theorem for the indexed base.

Part E:
Try to prove four-step return for indexed bases under the core-zero hypothesis.

Candidate theorem:

```lean id="xi7z5r"
theorem shiftedSemanticIndexedBase_add_four_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (k : ℕ) :
    shiftedSemanticIndexedBase r z (k + 4) =
      shiftedSemanticIndexedBase r z k
```

Expected route:
Use existing `semanticActIter_add_four_of_core_eq_zero` if available.

Part F:
If Part E succeeds, prove four-step return for shifted left endpoints and possibly for indexed paths.

Candidate theorem shapes:

```lean id="u0twjc"
theorem shiftedSemanticIndexedLeftEndpoint_add_four_of_core_eq_zero
    ...

theorem shiftedSemanticIndexedEdge_add_four_of_core_eq_zero
    ...
```

Do not force path equality if it becomes proof-heavy. Function-level equality is enough for this checkpoint.

Part G:
Update docs.

Update `DkReal.lean` and `design-phase-center-shift-104.md`.

Record the status clearly:

```text id="aqnc1v"
implemented:
  indexed shifted edge base
  indexed adjacent seam compatibility
  indexed center-to-next-action compatibility

implemented if successful:
  four-step return for indexed shifted bases and edges

remaining:
  explicit four-edge path concatenation or quotient cyclic parameter
  Euclidean one-eighth reading later
```

Required checks:

```text id="jaty8w"
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```
