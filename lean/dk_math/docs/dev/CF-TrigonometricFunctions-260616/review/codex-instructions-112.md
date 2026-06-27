# Codex instructions

Target:
DkMath.Analysis.DkReal.SemanticCF2DPhaseShift

Goal:
Continue checkpoint 104 by packaging `shiftedSemanticNormalizedEdge` toward the path/cyclic layer. First prove endpoint and seam-compatibility facts. Then, if the existing topology/path API makes it straightforward, package the shifted normalized edge as a topological path. Do not introduce Euclidean angle language yet.

Principle:
Keep this layer pre-geometric. Do not use angle, arc, degree, circle, rotation, piOverFour, or fortyFive in Lean theorem names. The goal is boundary-valued shifted paths, seam compatibility, and cyclic concatenation readiness.

Context:
`shiftedSemanticNormalizedEdge` is now implemented. Under the core-zero hypothesis, it preserves `q2`, starts at the left normalized center candidate, ends at the right normalized center candidate, and reaches the old seam at `phaseCenter`.

Part A:
Add direct endpoint and seam compatibility wrappers for downstream use.

Candidate theorem names:

```lean id="co7b8m"
theorem shiftedSemanticNormalizedEdge_leftEndpoint
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    shiftedSemanticNormalizedEdge r z 0 =
      shiftedSemanticLeftEndpoint r z

theorem shiftedSemanticNormalizedEdge_rightEndpoint
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    shiftedSemanticNormalizedEdge r z 1 =
      shiftedSemanticRightEndpoint r z
```

If these are already covered by simp theorems, add aliases only if they improve readability.

Part B:
Prove adjacent shifted-edge seam compatibility.

Expected theorem:

```lean id="t6wuof"
theorem shiftedSemanticNormalizedEdge_right_eq_next_left
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    shiftedSemanticNormalizedEdge r z 1 =
      shiftedSemanticNormalizedEdge r (semanticAct r z) 0
```

Expected route:
Use `shiftedSemanticNormalizedEdge_one`, `shiftedSemanticNormalizedEdge_zero`, and unfold the definitions of `shiftedSemanticRightEndpoint` and `shiftedSemanticLeftEndpoint`.

Part C:
Prove center-to-seam compatibility in a form useful for cyclic concatenation.

Candidate theorem:

```lean id="gl14am"
theorem shiftedSemanticNormalizedEdge_center_eq_semanticAct_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticNormalizedEdge r z phaseCenter =
      semanticAct r z
```

This can likely be a wrapper around `shiftedSemanticNormalizedEdge_center_eq_seam_of_core_eq_zero`.

Part D:
Inspect existing path packaging in nearby modules, especially `SemanticCF2DPath`, before introducing a new path definition.

If the existing pattern is straightforward, add a shifted path wrapper, for example:

```lean id="uln1ig"
def shiftedSemanticNormalizedPath
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) : Path
      (shiftedSemanticLeftEndpoint r z)
      (shiftedSemanticRightEndpoint r z) :=
  ...
```

Use the actual path type and existing topology conventions from the project.

If continuity proof is not straightforward, do not force it. Instead, add a precise TODO saying which continuity lemma or path wrapper is missing.

Part E:
If Part D succeeds, prove the q2 boundary theorem for the path values if the path API makes this convenient. Otherwise keep the existing function-level theorem as the main boundary law.

Candidate theorem shape:

```lean id="jvf9kp"
theorem shiftedSemanticNormalizedPath_q2_of_core_eq_zero
    ...
```

Part F:
Update docs.

Update `DkReal.lean` and `design-phase-center-shift-104.md`.

Record the status clearly:

```text id="kufx3f"
implemented:
  shifted normalized edge endpoint compatibility
  adjacent shifted-edge seam compatibility

implemented if successful:
  shiftedSemanticNormalizedPath

remaining:
  cyclic quotient parameter or four-edge shifted concatenation
  Euclidean one-eighth reading later
```

Required checks:

```text id="ziqod3"
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```
