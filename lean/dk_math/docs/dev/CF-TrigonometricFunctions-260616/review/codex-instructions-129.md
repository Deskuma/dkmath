# Codex instructions

Target:
DkMath.Analysis.DkReal.SemanticCF2DPhaseShift

Goal:
Continue checkpoint 104 by proving, or preparing, the bridge between the endpoint-casted older observed path and the canonical observed via-edge path. The key remaining issue is that descended semantic evaluation must commute with the canonical four-path concatenator.

Principle:
Keep this layer pre-geometric. Do not use angle, arc, degree, circle, rotation, piOverFour, or fortyFive in Lean theorem names. The goal is path-packaging compatibility between semantic evaluation and four-edge concatenation.

Context:
The endpoint mismatch has been isolated by:

```lean id="cg44s8"
shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint
shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_apply
```

The quotient closed path and finite closed path already match their canonical via-edge versions:

```lean id="wfkxy4"
shiftedCyclicFourPath_eq_viaEdges
shiftedSemanticFinFourLevelPath_eq_viaEdges
```

The canonical observed/direct comparison is already available:

```lean id="u4iljj"
shiftedSemanticObservedCyclicFourPathViaEdges_eq_finFourLevelPathViaEdges
```

The remaining bridge is:

```lean id="t4znju"
shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint
  =
shiftedSemanticObservedCyclicFourPathViaEdges
```

Part A:
First try the direct theorem.

```lean id="np5p0c"
theorem shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_eq_viaEdges
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint hcore z =
      shiftedSemanticObservedCyclicFourPathViaEdges hcore z
```

Expected route:
Use `Path.ext`.
Use `shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_apply`.
Use `shiftedCyclicFourPath_eq_viaEdges`.
Then unfold the canonical via-edge path only as much as needed.

If direct path equality is noisy, try value-level equality instead.

Part B:
Try a value-level bridge as fallback.

```lean id="h3vugz"
theorem shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_val_eq_viaEdges_val
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (t : unitInterval) :
    (shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint hcore z t).1 =
      (shiftedSemanticObservedCyclicFourPathViaEdges hcore z t).1
```

This may avoid some endpoint equality friction.

Part C:
If Part A or Part B is blocked, prove a smaller compatibility lemma for a single `Path.trans`.

Candidate direction:

```lean id="v4ygia"
theorem shiftedSemanticCyclicChartEval_trans_compat
    ...
```

Meaning:
Evaluating a `Path.trans` of quotient paths should agree with the `Path.trans` of the evaluated paths, after endpoint casts are aligned.

Do not make this fully generic if dependent endpoints become noisy. A specialized lemma for the current quotient edge paths is acceptable.

Part D:
Try a four-concat compatibility theorem specialized to the current case.

Candidate theorem:

```lean id="dczzau"
theorem shiftedSemanticCyclicChartEval_fourConcatWithSeams
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint hcore z =
      shiftedFourPathConcatWithSeams
        (shiftedSemanticObservedCyclicEdgePath hcore z (0 : Fin 4))
        (shiftedSemanticObservedCyclicEdgePath hcore z (1 : Fin 4))
        (shiftedSemanticObservedCyclicEdgePath hcore z (2 : Fin 4))
        (shiftedSemanticObservedCyclicEdgePath hcore z (3 : Fin 4))
        (shiftedSemanticFinRightLevelEndpoint_zero_eq_one_left hcore z)
        (shiftedSemanticFinRightLevelEndpoint_one_eq_two_left hcore z)
        (shiftedSemanticFinRightLevelEndpoint_two_eq_three_left hcore z)
        (shiftedSemanticFinRightLevelEndpoint_three_eq_zero_left hcore z)
```

This is essentially the same as Part A, but stated as evaluation-concat compatibility. Use whichever statement Lean accepts more naturally.

Part E:
If Part A succeeds, prove the final casted old-definition comparison.

```lean id="ab7wms"
theorem shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_eq_finFourLevelPath
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint hcore z =
      shiftedSemanticFinFourLevelPath hcore z := by
  calc
    shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint hcore z =
        shiftedSemanticObservedCyclicFourPathViaEdges hcore z := ...
    _ = shiftedSemanticFinFourLevelPathViaEdges hcore z :=
        shiftedSemanticObservedCyclicFourPathViaEdges_eq_finFourLevelPathViaEdges hcore z
    _ = shiftedSemanticFinFourLevelPath hcore z := by
        symm
        exact shiftedSemanticFinFourLevelPath_eq_viaEdges hcore z
```

Part F:
One-step-ahead experiment:
If the final casted comparison succeeds, also add a value-level final theorem.

```lean id="eeab91"
theorem shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_val_eq_finFourLevelPath_val
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (t : unitInterval) :
    (shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint hcore z t).1 =
      (shiftedSemanticFinFourLevelPath hcore z t).1 :=
  congrArg Subtype.val
    (congrFun
      (shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_eq_finFourLevelPath hcore z)
      t)
```

Part G:
If direct equality remains blocked, update the TODO precisely.

Use wording like:

```text id="ebt0p0"
The endpoint mismatch is solved. The remaining obstruction is the compatibility
of descended semantic evaluation with the nested `Path.trans` and `Path.cast`
structure of `shiftedFourPathConcatWithSeams`.
```

Part H:
Do not add Euclidean reading yet.

Part I:
Update docs.

Update `DkReal.lean` and `design-phase-center-shift-104.md`.

Record clearly:

```text id="b1oaqh"
implemented:
  endpoint-casted old observed path is stable
  direct or value-level bridge to canonical observed via-edge path if successful

implemented if successful:
  casted old observed path equals old finite four-level path
  value-level final comparison

remaining:
  evaluation-concat compatibility if not finished
  Euclidean one-eighth reading later
```

Required checks:

```text id="ufqcc5"
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```
