# Codex instructions

Target:
DkMath.Analysis.DkReal.SemanticCF2DPhaseShift

Goal:
Continue checkpoint 104 by introducing a canonical four-edge path concatenator. Use it to build comparison-friendly closed four paths from edge paths. Do not force equality between the existing closed paths yet if their nested `Path.trans` and `Path.cast` structures differ.

Principle:
Keep this layer pre-geometric. Do not use angle, arc, degree, circle, rotation, piOverFour, or fortyFive in Lean theorem names. The goal is path-packaging normalization between quotient traversal and fixed-boundary observation.

Context:
The single-edge comparison is now implemented:

```lean id="he6ork"
shiftedSemanticObservedCyclicEdgePath_eq_finLevelPath
```

The observed quotient path and the finite four-level path also have source and target comparison theorems, plus value-level endpoint comparisons. The remaining obstruction is not semantic. It is nested `Path.trans` and endpoint `Path.cast` normalization.

Part A:
Introduce a generic four-path concatenator.

Candidate definition shape:

```lean id="uv2f3o"
def shiftedFourPathConcat
    {α : Type _} [TopologicalSpace α]
    {a0 a1 a2 a3 a4 : α}
    (p0 : Path a0 a1)
    (p1 : Path a1 a2)
    (p2 : Path a2 a3)
    (p3 : Path a3 a4)
    (h40 : a4 = a0) :
    Path a0 a0 :=
  (p0.trans (p1.trans (p2.trans p3))).cast rfl h40
```

Alternative style:
If the existing code style uses `p0.trans (p1.cast ...)`, keep a helper closer to existing definitions. The key is to make one reusable standard concatenation form.

Part B:
If endpoints do not line up definitionally, use a version with explicit seam equalities.

Candidate definition shape:

```lean id="cq9c1t"
def shiftedFourPathConcatWithSeams
    {α : Type _} [TopologicalSpace α]
    {a0 b0 a1 b1 a2 b2 a3 b3 : α}
    (p0 : Path a0 b0)
    (p1 : Path a1 b1)
    (p2 : Path a2 b2)
    (p3 : Path a3 b3)
    (h01 : b0 = a1)
    (h12 : b1 = a2)
    (h23 : b2 = a3)
    (h30 : b3 = a0) :
    Path a0 a0 := by
  exact
    (((p0.trans (p1.cast h01 rfl)).trans
      (p2.cast h12 rfl)).trans
      (p3.cast h23 rfl)).cast rfl h30.symm
```

This shape mirrors the existing four-path definitions and may be easiest.

Part C:
Add source and target aliases for the generic concatenator only if useful.

Candidate theorem names:

```lean id="w7s4p5"
shiftedFourPathConcatWithSeams_source
shiftedFourPathConcatWithSeams_target
```

Part D:
Build a canonical observed four-edge path from the single-edge observed paths.

Candidate definition:

```lean id="kz5yas"
def shiftedSemanticObservedCyclicFourPathViaEdges
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    Path
      (shiftedSemanticFinLeftLevelEndpoint hcore z (0 : Fin 4))
      (shiftedSemanticFinLeftLevelEndpoint hcore z (0 : Fin 4)) := by
  let p0 := shiftedSemanticObservedCyclicEdgePath hcore z (0 : Fin 4)
  let p1 := shiftedSemanticObservedCyclicEdgePath hcore z (1 : Fin 4)
  let p2 := shiftedSemanticObservedCyclicEdgePath hcore z (2 : Fin 4)
  let p3 := shiftedSemanticObservedCyclicEdgePath hcore z (3 : Fin 4)
  exact shiftedFourPathConcatWithSeams
    p0 p1 p2 p3
    (shiftedSemanticFinRightLevelEndpoint_zero_eq_one_left hcore z)
    (shiftedSemanticFinRightLevelEndpoint_one_eq_two_left hcore z)
    (shiftedSemanticFinRightLevelEndpoint_two_eq_three_left hcore z)
    (shiftedSemanticFinRightLevelEndpoint_three_eq_zero_left hcore z)
```

Adjust names if the finite seam aliases require different theorem names.

Part E:
Build a canonical finite four-level path from direct finite level paths.

Candidate definition:

```lean id="hdkcup"
def shiftedSemanticFinFourLevelPathViaEdges
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    Path
      (shiftedSemanticFinLeftLevelEndpoint hcore z (0 : Fin 4))
      (shiftedSemanticFinLeftLevelEndpoint hcore z (0 : Fin 4)) := by
  let p0 := shiftedSemanticFinLevelPath hcore z (0 : Fin 4)
  let p1 := shiftedSemanticFinLevelPath hcore z (1 : Fin 4)
  let p2 := shiftedSemanticFinLevelPath hcore z (2 : Fin 4)
  let p3 := shiftedSemanticFinLevelPath hcore z (3 : Fin 4)
  exact shiftedFourPathConcatWithSeams
    p0 p1 p2 p3
    (shiftedSemanticFinRightLevelEndpoint_zero_eq_one_left hcore z)
    (shiftedSemanticFinRightLevelEndpoint_one_eq_two_left hcore z)
    (shiftedSemanticFinRightLevelEndpoint_two_eq_three_left hcore z)
    (shiftedSemanticFinRightLevelEndpoint_three_eq_zero_left hcore z)
```

Part F:
Prove canonical observed and canonical finite four paths are equal.

Candidate theorem:

```lean id="e49wod"
theorem shiftedSemanticObservedCyclicFourPathViaEdges_eq_finFourLevelPathViaEdges
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticObservedCyclicFourPathViaEdges hcore z =
      shiftedSemanticFinFourLevelPathViaEdges hcore z := by
  -- expected route:
  -- use shiftedSemanticObservedCyclicEdgePath_eq_finLevelPath for p0,p1,p2,p3
  -- then simplify if both definitions share the same concatenator
```

If direct rewriting is noisy, try `apply Path.ext; funext t` and use `shiftedPath_cast_apply` plus existing edge equality. If still noisy, stop and keep as TODO.

Part G:
Do not yet force comparison with the existing definitions:

```lean id="x0n779"
shiftedSemanticObservedCyclicFourPath
shiftedSemanticFinFourLevelPath
```

Instead, add TODOs:

```text id="t68n61"
Compare existing closed four-path definitions with the canonical via-edge versions after the common concatenator is stable.
```

Part H:
一歩先ゆくおまけ実験:
If Part F succeeds, try defining a generic congruence theorem for `shiftedFourPathConcatWithSeams`.

Candidate theorem direction:

```lean id="t4uo8r"
theorem shiftedFourPathConcatWithSeams_congr
    ...
```

It should say that if `p0 = q0`, `p1 = q1`, `p2 = q2`, and `p3 = q3`, then the concatenated closed paths are equal, assuming the same seam equalities. This theorem would make future comparisons much cleaner.

Do not spend too much time on this if dependent endpoints make it noisy.

Part I:
Update docs.

Update `DkReal.lean` and `design-phase-center-shift-104.md`.

Record clearly:

```text id="jv3piq"
implemented:
  generic four-path concatenator
  observed via-edge four path
  finite via-edge four path

implemented if successful:
  via-edge observed/direct four-path equality
  generic congruence theorem for four-path concatenator

remaining:
  compare existing closed paths with canonical via-edge paths
  nested Path.trans/cast normalization for old definitions
  Euclidean one-eighth reading later
```

Required checks:

```text id="j4iyhx"
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```
