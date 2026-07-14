# Codex instructions

Target:
DkMath.Analysis.DkReal.SemanticCF2DPhaseShift

Goal:
Continue checkpoint 104 by lifting the four edge-level mapping bridges through `shiftedFourPathConcatWithSeams`. The single-edge semantic mapping bridge is solved. The next target is a path-packaging theorem that transports mapped-edge equalities through the canonical four-edge concatenator while ignoring seam proof-term differences.

Principle:
Keep this layer pre-geometric. Do not use angle, arc, degree, circle, rotation, piOverFour, or fortyFive in Lean theorem names. The goal is path packaging and seam proof alignment only.

Context:
The edge-level mapping bridge is implemented:

```lean id="jbo91k"
shiftedSemanticCyclicChartEval_mappedEdge_eq_observedEdge
shiftedSemanticCyclicChartEval_mappedEdge_apply
shiftedSemanticCyclicChartEval_mappedEdge_zero_eq_observedEdge
shiftedSemanticCyclicChartEval_mappedEdge_one_eq_observedEdge
shiftedSemanticCyclicChartEval_mappedEdge_two_eq_observedEdge
shiftedSemanticCyclicChartEval_mappedEdge_three_eq_observedEdge
```

The path helpers are available:

```lean id="mj3a3z"
shiftedPath_map_cast
shiftedPath_map_trans
shiftedPath_cast_proof_irrel
shiftedFourPathConcatWithSeams
shiftedFourPathConcatWithSeams_congr
```

The remaining obstruction is lifting the four mapped-edge equalities through the nested `Path.trans` and `Path.cast` structure of `shiftedFourPathConcatWithSeams`.

Part A:
First try a stronger congruence theorem for the four-path concatenator that allows different seam proof terms.

Candidate theorem:

```lean id="ugxye0"
theorem shiftedFourPathConcatWithSeams_congr_cast_irrel
    {α : Type _} [TopologicalSpace α]
    {a0 b0 a1 b1 a2 b2 a3 b3 : α}
    {p0 q0 : Path a0 b0}
    {p1 q1 : Path a1 b1}
    {p2 q2 : Path a2 b2}
    {p3 q3 : Path a3 b3}
    (h01 k01 : b0 = a1)
    (h12 k12 : b1 = a2)
    (h23 k23 : b2 = a3)
    (h30 k30 : b3 = a0)
    (hp0 : p0 = q0)
    (hp1 : p1 = q1)
    (hp2 : p2 = q2)
    (hp3 : p3 = q3) :
    shiftedFourPathConcatWithSeams p0 p1 p2 p3 h01 h12 h23 h30 =
      shiftedFourPathConcatWithSeams q0 q1 q2 q3 k01 k12 k23 k30
```

Expected route:
Use `cases hp0`, `cases hp1`, `cases hp2`, `cases hp3`.
Then use `Path.ext`; `funext t`; simplify or use `shiftedPath_cast_proof_irrel`.
If proof irrelevance is still noisy, prove a pointwise version first.

Part B:
Try a map theorem for `shiftedFourPathConcatWithSeams`.

Candidate theorem direction:

```lean id="wavex3"
theorem shiftedFourPathConcatWithSeams_map
    {α β : Type _} [TopologicalSpace α] [TopologicalSpace β]
    {a0 b0 a1 b1 a2 b2 a3 b3 : α}
    (p0 : Path a0 b0)
    (p1 : Path a1 b1)
    (p2 : Path a2 b2)
    (p3 : Path a3 b3)
    (h01 : b0 = a1)
    (h12 : b1 = a2)
    (h23 : b2 = a3)
    (h30 : b3 = a0)
    (f : α → β) (hf : Continuous f) :
    (shiftedFourPathConcatWithSeams p0 p1 p2 p3 h01 h12 h23 h30).map hf =
      shiftedFourPathConcatWithSeams
        (p0.map hf)
        (p1.map hf)
        (p2.map hf)
        (p3.map hf)
        (by rw [h01])
        (by rw [h12])
        (by rw [h23])
        (by rw [h30])
```

Expected route:
Unfold `shiftedFourPathConcatWithSeams`.
Use `shiftedPath_map_trans` repeatedly.
Use `shiftedPath_map_cast`.
Use `shiftedPath_cast_proof_irrel` for final cast proof alignment.

If the fully generic theorem is too noisy, specialize it to `ShiftedCyclicChart` and `shiftedSemanticCyclicChartEval hcore z`.

Part C:
Create a mapped canonical quotient four-path theorem.

Candidate theorem:

```lean id="c8sbg5"
theorem shiftedSemanticCyclicChartEval_cyclicFourPathViaEdges_map_eq_mappedEdges
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    (shiftedCyclicFourPathViaEdges.map
      (continuous_shiftedSemanticCyclicChartEval hcore z)).cast
        (shiftedSemanticCyclicChartEval_left_zero hcore z).symm
        (shiftedSemanticCyclicChartEval_left_zero hcore z).symm =
      shiftedFourPathConcatWithSeams
        (((shiftedCyclicChartEdgePath (0 : Fin 4)).map
          (continuous_shiftedSemanticCyclicChartEval hcore z)).cast
            (shiftedSemanticCyclicChartEval_left hcore z (0 : Fin 4)).symm
            (shiftedSemanticCyclicChartEval_right hcore z (0 : Fin 4)).symm)
        (((shiftedCyclicChartEdgePath (1 : Fin 4)).map
          (continuous_shiftedSemanticCyclicChartEval hcore z)).cast
            (shiftedSemanticCyclicChartEval_left hcore z (1 : Fin 4)).symm
            (shiftedSemanticCyclicChartEval_right hcore z (1 : Fin 4)).symm)
        (((shiftedCyclicChartEdgePath (2 : Fin 4)).map
          (continuous_shiftedSemanticCyclicChartEval hcore z)).cast
            (shiftedSemanticCyclicChartEval_left hcore z (2 : Fin 4)).symm
            (shiftedSemanticCyclicChartEval_right hcore z (2 : Fin 4)).symm)
        (((shiftedCyclicChartEdgePath (3 : Fin 4)).map
          (continuous_shiftedSemanticCyclicChartEval hcore z)).cast
            (shiftedSemanticCyclicChartEval_left hcore z (3 : Fin 4)).symm
            (shiftedSemanticCyclicChartEval_right hcore z (3 : Fin 4)).symm)
        (shiftedSemanticCyclicChartEval_seam_zero_value hcore z)
        (shiftedSemanticCyclicChartEval_seam_one_value hcore z)
        (shiftedSemanticCyclicChartEval_seam_two_value hcore z)
        (shiftedSemanticCyclicChartEval_seam_three_value hcore z)
```

Adjust equality directions as needed. This theorem may be easier after Part B.

Part D:
Use mapped-edge equalities to prove the canonical observed via-edge theorem.

Candidate theorem:

```lean id="nrmv8z"
theorem shiftedSemanticCyclicChartEval_cyclicFourPathViaEdges_map_eq_observedViaEdges
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    (shiftedCyclicFourPathViaEdges.map
      (continuous_shiftedSemanticCyclicChartEval hcore z)).cast
        (shiftedSemanticCyclicChartEval_left_zero hcore z).symm
        (shiftedSemanticCyclicChartEval_left_zero hcore z).symm =
      shiftedSemanticObservedCyclicFourPathViaEdges hcore z
```

Expected route:
Use Part C.
Then use `shiftedFourPathConcatWithSeams_congr_cast_irrel` or existing congr theorem plus proof irrelevance.
Apply the four mapped-edge equality aliases.

Part E:
Connect the endpoint-casted old observed path to canonical observed via-edge path.

Candidate theorem:

```lean id="z0g9ei"
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
Use Part D.

If full path equality is noisy, prove value-level equality first.

Part F:
If Part E succeeds, prove the final casted comparison.

```lean id="wkfv68"
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

Part G:
One-step-ahead experiment:
If the final casted comparison succeeds, add the value-level final theorem.

```lean id="comopz"
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

Part H:
One-step-ahead inference:
If Part B succeeds generically, consider moving `shiftedFourPathConcatWithSeams_map` and `shiftedFourPathConcatWithSeams_congr_cast_irrel` near the generic four-path concatenator section, not near semantic-specific theorems. This will make the path-packaging API reusable for future DkMath path constructions.

Part I:
If the bridge remains blocked, update the TODO precisely:

```text id="j8uc55"
The single-edge mapping bridge is solved. The remaining obstruction is lifting
the four mapped-edge comparisons through `shiftedFourPathConcatWithSeams`,
specifically normalizing the mapped canonical quotient four-edge path into the
canonical observed via-edge concatenation.
```

Part J:
Do not add Euclidean reading yet.

Part K:
Update docs.

Update `DkReal.lean`, `design-phase-center-shift-104.md`, and optionally add a short dev report if a major bridge succeeds or a precise obstruction remains.

Record clearly:

```text id="rfrj33"
implemented:
  four-path concat congr with cast-proof irrelevance
  four-path concat map theorem if successful
  mapped canonical quotient four-path theorem if successful

implemented if successful:
  endpoint-casted old observed path equals canonical observed via-edge path
  endpoint-casted old observed path equals finite four-level path
  value-level final comparison

remaining:
  generic four-concat map theorem if deferred
  Euclidean one-eighth reading later
```

Required checks:

```text id="bcpodf"
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```
