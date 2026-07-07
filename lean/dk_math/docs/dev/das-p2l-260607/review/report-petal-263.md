# Report: petal-263

## Goal

Create the first pair-comparison-facing surface from:

```lean
SourcePressureForwardBoxComparisonState
```

The new surface should package the forward branch together with the adjacent
pair and both endpoint pulse boxes.

## Implemented

Added in `DkMath.Collatz.PetalBridge.PressureState`:

```lean
def SourcePressureForwardPairComparisonState
```

The state stores:

```lean
SourcePressureForwardBoxComparisonState L W W'
SourcePressureLocalIslandWitnessAdjacentPairInList L W W'
SourcePressureBeamCenteredLocalPulseBox n k r L W
SourcePressureBeamCenteredLocalPulseBox n k r L W'
```

Projection lemmas:

```lean
theorem SourcePressureForwardPairComparisonState.forward
theorem SourcePressureForwardPairComparisonState.adjacentPair
theorem SourcePressureForwardPairComparisonState.left_box
theorem SourcePressureForwardPairComparisonState.right_box
theorem SourcePressureForwardPairComparisonState.val_lt
theorem SourcePressureForwardPairComparisonState.not_reverse_box
```

Constructor:

```lean
theorem SourcePressureForwardBoxComparisonState.to_pairComparisonState
```

## Meaning

The forward branch now has a dedicated pair-comparison-facing state:

```text
FBC -> ForwardPairComparisonState
```

This is still a local witness-pair object.  It does not decide the overlap
branch and does not merge diagnostics with obstructions.

## Guardrails

The state duplicates data available from `FBC` intentionally.  The purpose is
API stability: later pair-comparison theorems can consume
`SourcePressureForwardPairComparisonState` without depending on how
`SourcePressureForwardBoxComparisonState` is represented internally.

No new global claim is introduced.  There is no coverage, canonical selection,
propagation, overlap repair, or convergence statement.

## Verification

Commands run from `lean/dk_math`:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
```

Both builds completed successfully.

`git diff --check` is run as the final whitespace gate.

## Next Branch Prediction

The immediate next lift is:

```text
S/R/B + sorted(L)
  -> ForwardPairComparisonState or PairOverlapObstruction
```

This should reuse the existing named split:

```lean
sourcePressure..._to_forwardBoxComparisonState_or_pairOverlap
```

and apply:

```lean
SourcePressureForwardBoxComparisonState.to_pairComparisonState
```

on the forward branch.
