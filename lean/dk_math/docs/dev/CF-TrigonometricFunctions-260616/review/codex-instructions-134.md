# Codex instructions

## Codex 指示書

Target:
DkMath.Analysis.DkReal.SemanticCF2DPhaseShift

Goal:
Continue checkpoint 104 by proving the global map-through-gluing theorem. The edgewise mapped quotient four-edge path is already equal to the canonical observed via-edge path. The remaining task is to show that mapping the already-glued quotient four-path is equal to gluing the four mapped quotient edges.

Principle:
Keep this layer pre-geometric. Do not use angle, arc, degree, circle, rotation, piOverFour, or fortyFive in Lean theorem names. The goal is path packaging normalization for Mathlib `Path`.

Context:
The following theorem is implemented:

```lean id="hly2rb"
shiftedFourPathConcatWithSeams_congr_cast_irrel
```

The following theorem is implemented:

```lean id="zlik52"
shiftedSemanticCyclicChartEval_mappedEdges_eq_observedViaEdges
```

This means the four mapped quotient edges, after endpoint relabelling and gluing, equal the canonical observed semantic via-edge path.

The remaining target is:

```text id="c22miz"
map the already-glued quotient four-path
  =
glue the four mapped quotient edges
```

Part A:
Try a generic map theorem for the four-path concatenator.

Candidate theorem:

```lean id="m55y5n"
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
Use `shiftedPath_map_trans`.
Use `shiftedPath_map_cast`.
Use `shiftedPath_cast_proof_irrel` or `shiftedFourPathConcatWithSeams_congr_cast_irrel` if proof terms differ.
If full path equality is noisy, prove pointwise equality with `Path.ext` and `funext t`.

Part B:
If Part A is too hard generically, prove the semantic-specialized theorem.

Candidate theorem:

```lean id="efc6l7"
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
        (shiftedSemanticFinRightLevelEndpoint_zero_eq_one_left hcore z)
        (shiftedSemanticFinRightLevelEndpoint_one_eq_two_left hcore z)
        (shiftedSemanticFinRightLevelEndpoint_two_eq_three_left hcore z)
        (shiftedSemanticFinRightLevelEndpoint_three_eq_zero_left hcore z)
```

Adjust equality directions as required by `Path.cast`.

Part C:
Use the mapped-edges theorem to prove the canonical observed via-edge bridge.

Candidate theorem:

```lean id="fvc3bd"
theorem shiftedSemanticCyclicChartEval_cyclicFourPathViaEdges_map_eq_observedViaEdges
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    (shiftedCyclicFourPathViaEdges.map
      (continuous_shiftedSemanticCyclicChartEval hcore z)).cast
        (shiftedSemanticCyclicChartEval_left_zero hcore z).symm
        (shiftedSemanticCyclicChartEval_left_zero hcore z).symm =
      shiftedSemanticObservedCyclicFourPathViaEdges hcore z := by
  calc
    (shiftedCyclicFourPathViaEdges.map
      (continuous_shiftedSemanticCyclicChartEval hcore z)).cast
        (shiftedSemanticCyclicChartEval_left_zero hcore z).symm
        (shiftedSemanticCyclicChartEval_left_zero hcore z).symm =
        shiftedFourPathConcatWithSeams
          ...
          ...
          ...
          ...
          (shiftedSemanticFinRightLevelEndpoint_zero_eq_one_left hcore z)
          (shiftedSemanticFinRightLevelEndpoint_one_eq_two_left hcore z)
          (shiftedSemanticFinRightLevelEndpoint_two_eq_three_left hcore z)
          (shiftedSemanticFinRightLevelEndpoint_three_eq_zero_left hcore z) := ...
    _ = shiftedSemanticObservedCyclicFourPathViaEdges hcore z :=
        shiftedSemanticCyclicChartEval_mappedEdges_eq_observedViaEdges hcore z
```

Part D:
Connect old quotient closed path to canonical quotient via-edge path.

Use the existing theorem:

```lean id="sfe9ev"
shiftedCyclicFourPath_eq_viaEdges
```

Then prove the endpoint-casted observed old path equals canonical observed via-edge path.

Candidate theorem:

```lean id="za32co"
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

If path equality is noisy, prove a value-level theorem first.

Part E:
If Part D succeeds, prove the final comparison to the old finite four-level path.

Candidate theorem:

```lean id="cvz84i"
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
One-step-ahead inference:
If `shiftedFourPathConcatWithSeams_map` succeeds generically, move it near the generic four-path concatenator section. This theorem should become part of the reusable DkMath path-packaging API.

Part G:
One-step-ahead experiment:
Create a tiny prototype section for a future DkPath wrapper, without changing public semantics.

Do not implement a full DkPath yet. Only add a comment or TODO block if useful.

Suggested design note:

```text id="x2u9ky"
Future DkPath should separate:
  trace
  endpoint labels
  seam witnesses

Public API should expose:
  map_cast
  map_trans
  cast_proof_irrel
  four_concat_congr_cast_irrel
  four_concat_map
```

Part H:
If the global bridge remains blocked, update the TODO precisely:

```text id="evj97t"
The mapped-edge four-concat is equal to the canonical observed via-edge path.
The remaining obstruction is the global map-through-gluing normalization:
mapping `shiftedCyclicFourPathViaEdges` should equal gluing the mapped quotient
edges.
```

Part I:
Do not add Euclidean reading yet.

Part J:
Update docs.

Update `DkReal.lean`, `design-phase-center-shift-104.md`, and the dev report if a major theorem succeeds or a precise obstruction remains.

Required checks:

```text id="i9pou3"
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```
