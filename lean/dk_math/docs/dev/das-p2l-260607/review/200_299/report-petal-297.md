# Petal Checkpoint 297 Report

## Implemented

The finite-window pressure layer now records the polarity check requested at
cp-296 in `PressureState/FiniteWindowPacking.lean`.

Added:

- `sourcePressureSortedBefore_not_failure`
- `sourcePressureAdjacentDiagnosis_not_of_sorted_adjacent`
- `sourcePressureCanonicalFiniteWindowPackingState_false_of_sorted`

## Fact established by Lean

For an explicitly supplied local-island witness list `L`:

1. `SourcePressureLocalIslandWitnessListSortedBefore L` excludes
   `SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L`.
2. Therefore an adjacent diagnosis cannot coexist with sorted adjacency.  In
   the recovered branch, sortedness gives `W Before W'` while the diagnosis
   stores `W' Before W`; positive interval lengths make these incompatible.
   In the overlap branch, the stored adjacent-overlap obstruction produces a
   sorted-before failure, which is excluded by the first fact.
3. Any canonical finite-window packing state for an adjacent pair is therefore
   false under the same sortedness, endpoint-window, and adjacency hypotheses.

This is a genuine polarity result, not a numerical experiment.  It shows that
the previous canonical packing route is a failure-resolution route and cannot
be consumed as a sorted witness-family route without changing one of its
contracts.

## Scope boundary

No universal producer for `AdjacentDiagnosis` was added.  No global coverage,
Collatz convergence, or unconditional finite-window estimate follows from
this checkpoint.  Existing APIs remain unchanged; the new results are
negative compatibility lemmas.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```

The repository still has the pre-existing unrelated `sorry` warning in
`DkMath.NumberTheory.ZsigmondyCyclotomicResearch`.lean`.

## Next implementation direction

Build the nonvacuous branch without diagnosis data:

1. define a sorted adjacent pulse-pair carrier containing only adjacency and
   the two local pulse boxes;
2. construct each pulse box from explicit witness membership;
3. prove the direct two-spacing theorem for sorted adjacent centers;
4. apply the existing finite two-separated-set bound to actual positive center
   coordinates;
5. only then add the direct sign-capacity injection and local Big surface.

The old diagnosis/canonical family should remain available as a historical
failure-resolution API, but it should not be used as the premise of the new
sorted packing theorems.
