# Codex instructions

Target:
DkMath.Analysis.DkReal.SemanticCF2DPhaseShift

Goal:
Continue checkpoint 104 by turning the seam-alignment infrastructure into an actual mapping bridge. First compare mapped quotient edge paths with the canonical observed edge paths. Then use those edge-level facts to attack the four-concat compatibility theorem.

Principle:
Keep this layer pre-geometric. Do not use angle, arc, degree, circle, rotation, piOverFour, or fortyFive in Lean theorem names. The goal is path packaging and seam proof alignment only.

Context:
The following helpers are now implemented:

```lean id="p329jw"
shiftedPath_map_cast
shiftedPath_map_trans
shiftedPath_cast_proof_irrel
```

The quotient endpoint evaluation aliases are available, including:

```lean id="shl2hd"
shiftedSemanticCyclicChartEval_right_zero
shiftedSemanticCyclicChartEval_left_one
shiftedSemanticCyclicChartEval_right_one
shiftedSemanticCyclicChartEval_left_two
shiftedSemanticCyclicChartEval_right_two
shiftedSemanticCyclicChartEval_left_three
shiftedSemanticCyclicChartEval_right_three
```

The finite seam value aliases are available:

```lean id="k2c2ix"
shiftedSemanticCyclicChartEval_seam_zero_value
shiftedSemanticCyclicChartEval_seam_one_value
shiftedSemanticCyclicChartEval_seam_two_value
shiftedSemanticCyclicChartEval_seam_three_value
```

The remaining obstruction is not semantic. It is aligning the endpoint equality proofs produced by mapping quotient seams with the finite seam equality proofs used by the canonical via-edge concatenator.

Part A:
Define or prove a theorem for mapped quotient edge paths.

Candidate theorem:

```lean id="n6eg7b"
theorem shiftedSemanticCyclicChartEval_mappedEdge_eq_observedEdge
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) :
    ((shiftedCyclicChartEdgePath i).map
      (continuous_shiftedSemanticCyclicChartEval hcore z)).cast
        (shiftedSemanticCyclicChartEval_left hcore z i)
        (shiftedSemanticCyclicChartEval_right hcore z i) =
      shiftedSemanticObservedCyclicEdgePath hcore z i
```

Adjust the direction of the `Path.cast` equality arguments to match the actual `Path.cast` API. If the path equality is noisy, prove a pointwise theorem first.

Candidate pointwise theorem:

```lean id="cxd6hg"
theorem shiftedSemanticCyclicChartEval_mappedEdge_apply
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) (t : unitInterval) :
    (((shiftedCyclicChartEdgePath i).map
      (continuous_shiftedSemanticCyclicChartEval hcore z)).cast
        (shiftedSemanticCyclicChartEval_left hcore z i)
        (shiftedSemanticCyclicChartEval_right hcore z i) t)
      =
    shiftedSemanticObservedCyclicEdgePath hcore z i t
```

Part B:
If Part A is blocked by cast proof directions, add concrete aliases for each mapped edge.

Candidate names:

```lean id="ldgw7e"
shiftedSemanticCyclicChartEval_mappedEdge_zero_eq_observedEdge
shiftedSemanticCyclicChartEval_mappedEdge_one_eq_observedEdge
shiftedSemanticCyclicChartEval_mappedEdge_two_eq_observedEdge
shiftedSemanticCyclicChartEval_mappedEdge_three_eq_observedEdge
```

Concrete versions may be easier because the endpoint aliases are already concrete.

Part C:
Try a specialized four-concat map theorem using the existing quotient canonical path.

Candidate theorem:

```lean id="bdyye1"
theorem shiftedSemanticCyclicChartEval_cyclicFourPathViaEdges_map_eq_observedViaEdges
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    ((shiftedCyclicFourPathViaEdges).map
      (continuous_shiftedSemanticCyclicChartEval hcore z)).cast
        (shiftedSemanticCyclicChartEval_left_zero hcore z)
        (shiftedSemanticCyclicChartEval_left_zero hcore z)
      =
    shiftedSemanticObservedCyclicFourPathViaEdges hcore z
```

Adjust equality directions to match `Path.cast`.

Expected route:
Use `shiftedPath_map_trans` repeatedly.
Use `shiftedPath_map_cast`.
Use `shiftedPath_cast_proof_irrel` to ignore seam proof-term differences.
Use the mapped-edge equality from Part A or Part B.

Part D:
Use the old-to-canonical quotient path equality to connect the endpoint-casted old observed path.

Candidate theorem:

```lean id="v9lyij"
theorem shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_eq_viaEdges
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint hcore z =
      shiftedSemanticObservedCyclicFourPathViaEdges hcore z
```

Expected route:
Use `shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_apply`.
Use `shiftedCyclicFourPath_eq_viaEdges`.
Use Part C.

If full path equality is noisy, prove value-level equality first:

```lean id="athhw6"
theorem shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint_val_eq_viaEdges_val
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (t : unitInterval) :
    (shiftedSemanticObservedCyclicFourPathAsFiniteEndpoint hcore z t).1 =
      (shiftedSemanticObservedCyclicFourPathViaEdges hcore z t).1
```

Part E:
If Part D succeeds, prove the final casted comparison.

```lean id="o8zzs5"
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
Try a generic map theorem for the four-path concatenator only after the specialized theorem succeeds.

Candidate direction:

```lean id="fzcwak"
theorem shiftedFourPathConcatWithSeams_map
    ...
```

It should state that mapping a seam-glued four-path equals the seam-glued path of mapped components, up to endpoint cast proof irrelevance.

Do not force this if dependent endpoints become noisy. The specialized semantic theorem is more important.

Part G:
If the bridge remains blocked, update the TODO precisely:

```text id="le89jv"
Endpoint evaluation aliases, finite seam value aliases, map/cast/trans helpers,
and cast proof irrelevance are available. The remaining obstruction is applying
these to normalize the mapped canonical four-edge concatenator into the
canonical observed via-edge concatenator.
```

Part H:
Do not add Euclidean reading yet.

Part I:
Update docs.

Update `DkReal.lean` and `design-phase-center-shift-104.md`.

Record clearly:

```text id="r6x26m"
implemented:
  mapped-edge to observed-edge comparison
  mapped canonical quotient four-path to observed via-edge comparison

implemented if successful:
  endpoint-casted old observed path equals canonical observed via-edge path
  final casted observed path equals finite four-level path
  value-level final comparison

remaining:
  generic four-concat map theorem if not added
  Euclidean one-eighth reading later
```

Required checks:

```text id="fy7y1d"
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```
