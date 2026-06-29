# Codex instructions

Target:
DkMath.Analysis.DkReal.SemanticCF2DPhaseShift

Goal:
Continue checkpoint 104 by bridging the older observed closed path to the canonical observed via-edge path. Do not force the final theorem until endpoint casts and evaluation-concatenation compatibility are stable.

Principle:
Keep this layer pre-geometric. Do not use angle, arc, degree, circle, rotation, piOverFour, or fortyFive in Lean theorem names. The goal is to commute descended semantic evaluation with the canonical four-edge path packaging.

Context:
The following old-to-canonical facts are implemented:

```lean id="hku8kp"
shiftedCyclicFourPath_eq_viaEdges
shiftedSemanticFinFourLevelPath_eq_viaEdges
```

The canonical observed/direct comparison is also implemented:

```lean id="eqekkk"
shiftedSemanticObservedCyclicFourPathViaEdges_eq_finFourLevelPathViaEdges
```

The remaining bridge is the older observed path:

```lean id="xduybw"
shiftedSemanticObservedCyclicFourPath
```

It is defined by evaluating the already-concatenated quotient closed path. The canonical observed via-edge path evaluates each quotient edge first and then concatenates the resulting fixed-boundary edge paths.

Part A:
First define an endpoint-casted old observed path whose endpoints match the finite left endpoint.

Candidate definition:

```lean id="zhgyfc"
def shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    Path
      (shiftedSemanticFinLeftLevelEndpoint hcore z (0 : Fin 4))
      (shiftedSemanticFinLeftLevelEndpoint hcore z (0 : Fin 4)) :=
  (shiftedSemanticObservedCyclicFourPath hcore z).cast
    (shiftedSemanticCyclicChartEval_left_zero hcore z)
    (shiftedSemanticCyclicChartEval_left_zero hcore z)
```

Adjust the direction of the equality arguments to match `Path.cast`. The existing helper `shiftedPath_cast_apply` can help if needed.

Part B:
Add source, target, and apply/cast theorem for the casted old observed path.

Candidate theorem names:

```lean id="kc6wo3"
shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_source
shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_target
shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_apply
```

The apply theorem should expose that casting does not change pointwise values.

Candidate shape:

```lean id="cehjtt"
theorem shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_apply
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (t : unitInterval) :
    shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint hcore z t =
      shiftedSemanticObservedCyclicFourPath hcore z t := by
  ...
```

If the equality direction is inconvenient due to dependent endpoints, prove the value-level version using `Subtype.val`.

Part C:
Try to prove that the endpoint-casted old observed path equals the canonical observed via-edge path.

Candidate theorem:

```lean id="d8kkg9"
theorem shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_eq_viaEdges
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint hcore z =
      shiftedSemanticObservedCyclicFourPathViaEdges hcore z
```

Expected route:
Use `shiftedCyclicFourPath_eq_viaEdges` and the fact that evaluation of each quotient edge path equals the observed cyclic edge path. If direct equality is noisy, try `Path.ext` and then use `shiftedPath_cast_apply`.

Part D:
If Part C is too hard, prove a value-level theorem first.

Candidate theorem:

```lean id="e3g17v"
theorem shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_val_eq_viaEdges_val
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (t : unitInterval) :
    (shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint hcore z t).1 =
      (shiftedSemanticObservedCyclicFourPathViaEdges hcore z t).1
```

Part E:
一歩先ゆくおまけ実験:
Try a local evaluation-concat compatibility lemma specialized to the canonical four-path concatenator.

Candidate direction:

```lean id="xjg63p"
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

This is essentially the same as Part C, but stated as a map-concat compatibility theorem. Use whichever statement Lean accepts more naturally.

Part F:
If Part C succeeds, prove the final old-definition comparison.

Candidate theorem:

```lean id="eiruma"
theorem shiftedSemanticObservedCyclicFourPath_eq_finFourLevelPath_after_cast
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

Part G:
If full path equality remains noisy, keep the TODO precise:

```text id="hqwd4d"
The old quotient path and old finite path match their canonical via-edge versions.
The remaining bridge is commuting descended semantic evaluation with
`shiftedFourPathConcatWithSeams`, after endpoint casting from the observed
quotient-left endpoint to the finite left endpoint.
```

Part H:
Do not add Euclidean reading yet.

Part I:
Update docs.

Update `DkReal.lean` and `design-phase-center-shift-104.md`.

Record clearly:

```text id="thl8ee"
implemented:
  endpoint-casted old observed path
  source/target/apply aliases for casted observed path

implemented if successful:
  casted old observed path equals canonical observed via-edge path
  final casted old observed path equals old finite four-level path
  value-level final theorem

remaining:
  evaluation-commutes-with-four-path-concat if not finished
  Euclidean one-eighth reading later
```

Required checks:

```text id="rglpes"
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```
