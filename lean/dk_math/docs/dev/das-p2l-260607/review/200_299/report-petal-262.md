# Report: petal-262

## Goal

Add convenience projections from:

```lean
SourcePressureForwardBoxComparisonState
```

so the named state is ready to serve as a pair-comparison-layer input.

## Implemented

Added in `DkMath.Collatz.PetalBridge.PressureState`:

```lean
theorem SourcePressureForwardBoxComparisonState.left_box
theorem SourcePressureForwardBoxComparisonState.right_box
theorem SourcePressureForwardBoxComparisonState.adjacentPair
theorem SourcePressureForwardBoxComparisonState.left_mem
theorem SourcePressureForwardBoxComparisonState.right_mem
```

These complement the existing projections:

```lean
theorem SourcePressureForwardBoxComparisonState.box
theorem SourcePressureForwardBoxComparisonState.val_lt
theorem SourcePressureForwardBoxComparisonState.not_reverse_box
```

## Meaning

`SourcePressureForwardBoxComparisonState` now exposes all local data expected by
the next pair-comparison layer:

```text
FBC
  -> Box
  -> left/right pulse boxes
  -> AdjacentPairInList
  -> W in L, W' in L
  -> W.val < W'.val
  -> not reverse Box
```

Callers can stay at the named-state level and project exactly the local fact
they need without unpacking the conjunction manually.

## Guardrails

These are pure projection lemmas.  They add no new mathematical strength beyond
the already stored `SourcePressureForwardBoxComparisonState`.

They do not assert global coverage, canonical pair selection, propagation,
overlap repair, or convergence.

## Verification

Commands run from `lean/dk_math`:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
```

Both builds completed successfully.

`git diff --check` is run as the final whitespace gate.

## Next Branch Prediction

The named forward branch is now complete enough to feed a real pair-comparison
surface.

Candidate next step:

```text
ForwardBoxComparisonState L W W'
  -> pair-comparison-facing facts for W and W'
```

The total state split should continue to keep the obstruction branch separate:

```text
ForwardBoxComparisonState or PairOverlapObstruction
```

rather than coercing overlap into a diagnostic branch.
