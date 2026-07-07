# Report: petal-264

## Goal

Lift the named forward-box split to the forward-pair-comparison state.

Target surface:

```text
FailureResolution + sorted(L)
  -> ForwardPairComparisonState ∨ PairOverlapObstruction

SortedFailure + sorted(L)
  -> ForwardPairComparisonState ∨ PairOverlapObstruction

BeamSeed + sorted(L)
  -> ForwardPairComparisonState ∨ PairOverlapObstruction
```

## Implemented

Added the following theorems in
`DkMath.Collatz.PetalBridge.PressureState`:

```lean
sourcePressureFailureResolutionState_to_forwardPairComparisonState_or_pairOverlap
sourcePressureSortedFailureState_to_forwardPairComparisonState_or_pairOverlap
sourcePressureBeamSeedState_to_forwardPairComparisonState_or_pairOverlap
```

The implementation reuses the existing forward-box split:

```lean
sourcePressureFailureResolutionState_to_forwardBoxComparisonState_or_pairOverlap
sourcePressureSortedFailureState_to_forwardBoxComparisonState_or_pairOverlap
sourcePressureBeamSeedState_to_forwardBoxComparisonState_or_pairOverlap
```

and converts the forward branch by:

```lean
SourcePressureForwardBoxComparisonState.to_pairComparisonState
```

The overlap obstruction branch is passed through unchanged.

## Meaning

The pair-comparison layer now has a clean entry point.

Instead of making callers unpack a `ForwardBoxComparisonState` and then convert
it locally, the state ladder provides the pair-facing branch directly:

```text
state ladder
  -> ForwardPairComparisonState
     or concrete PairOverlapObstruction
```

This keeps the main branch and the obstruction branch separated.  The forward
branch is now ready for comparison lemmas that consume:

- adjacent-pair address data;
- left and right centered pulse boxes;
- forward value order;
- reverse-box exclusion.

## Guardrails

This checkpoint is only a packaging and lift step.

It does not assert:

- global coverage;
- canonical witness selection;
- overlap repair;
- propagation beyond the explicit adjacent pair;
- Collatz convergence.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
```

`git diff --check` is part of the final gate for this checkpoint.

## Next Branch Prediction

The next natural branch is to add convenience projections from
`SourcePressureForwardPairComparisonState`, mirroring the already useful
`ForwardBoxComparisonState` surface.

Candidate projections:

```lean
SourcePressureForwardPairComparisonState.left_mem
SourcePressureForwardPairComparisonState.right_mem
SourcePressureForwardPairComparisonState.left_signs
SourcePressureForwardPairComparisonState.right_signs
```

The strongest immediate target is probably to expose the sign/height/jump
payload already stored in the two endpoint boxes, while keeping the pair-overlap
obstruction branch separate.
