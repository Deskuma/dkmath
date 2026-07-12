# Report: petal-260

## Goal

Lift the existing boxed diagnostic / pair-overlap obstruction split into a
comparison-ready split under sortedness.

Target shape:

```text
FailureResolution + sorted(L)
  -> ForwardBoxComparison or PairOverlapObstruction
```

with wrappers for `SortedFailureState` and `BeamSeedState` if they close
cleanly.

## Implemented

Added in `DkMath.Collatz.PetalBridge.PressureState`:

```lean
theorem sourcePressureFailureResolutionState_to_forwardBoxComparison_or_pairOverlap
theorem sourcePressureSortedFailureState_to_forwardBoxComparison_or_pairOverlap
theorem sourcePressureBeamSeedState_to_forwardBoxComparison_or_pairOverlap
```

The boxed branch now carries:

```lean
SourcePressureOrientedNeighborBoxState L W W'
W.val < W'.val
not SourcePressureOrientedNeighborBoxState L W' W
```

The obstruction branch remains unchanged:

```lean
exists A B,
  SourcePressureLocalIslandWitnessAdjacentPairInList L A B
    and SourcePressureLocalIslandWitnessPairOverlapObstruction A B
```

## Meaning

The state ladder now has comparison-ready public surfaces:

```text
FailureResolution + sorted(L)
  -> ForwardBoxComparison or PairOverlapObstruction

SortedFailure + sorted(L)
  -> ForwardBoxComparison or PairOverlapObstruction

BeamSeed + sorted(L)
  -> ForwardBoxComparison or PairOverlapObstruction
```

This separates the two downstream cases cleanly:

* `Box` side: forward value order is fixed and reverse box orientation is
  impossible.
* `PairOverlap` side: the local obstruction is preserved as an explicit
  adjacent-pair obstruction.

## Guardrails

The sortedness hypothesis is explicit because the forward value comparison is
not a consequence of failure resolution, sorted failure, or Beam seed alone.

These theorems do not repair overlaps, do not choose a canonical adjacent pair,
do not prove list coverage, and do not propagate the local comparison beyond
the two witnesses.

## Verification

Commands run from `lean/dk_math`:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
```

Both builds completed successfully.

`git diff --check` is run as the final whitespace gate.

## Next Branch Prediction

The comparison-ready split is now ready to be consumed by the pair-comparison
layer.

Natural next theorem shape:

```text
BeamSeed + sorted(L)
  -> forward comparison data or explicit overlap obstruction
  -> caller-specific pair comparison surface
```

If a caller only needs the forward branch, it should consume the boxed branch
directly.  If it needs total case analysis, it should keep the pair-overlap
obstruction separate instead of coercing it into a diagnostic branch.
