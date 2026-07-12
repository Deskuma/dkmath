# Report: petal-254

## Goal

Add projection lemmas for `SourcePressureOrientedNeighborBoxState`.

## Implemented

Added in `DkMath.Collatz.PetalBridge.PressureState`:

```lean
theorem SourcePressureOrientedNeighborBoxState.diagnostic
theorem SourcePressureOrientedNeighborBoxState.left_box
theorem SourcePressureOrientedNeighborBoxState.right_box
```

These project the three stored components of the two-endpoint box:

```text
Box(W,W') -> D(W,W')
Box(W,W') -> left endpoint pulse box W
Box(W,W') -> right endpoint pulse box W'
```

## Extra Comparison Hook

Also added the next natural orientation projections:

```lean
theorem SourcePressureOrientedNeighborDiagnosticState.adjacentPair
theorem SourcePressureOrientedNeighborBoxState.adjacentPair
```

These establish the comparison-ready path:

```text
Box(W,W') -> D(W,W') -> AdjacentPairInList L W W'
```

## Meaning

The two-endpoint box is now usable as a caller-facing surface.  Downstream
proofs no longer need to destruct the box manually to access the diagnostic,
the left endpoint local box, the right endpoint local box, or the ordered
adjacent-pair address.

## Next Direction

The natural next comparison layer is:

```text
Box(W,W')
  -> signs(W)
  -> signs(W')
  -> AdjacentPairInList L W W'
  -> compare W.val and W'.val
```

This checkpoint prepared the projection API required for that move.

## Guardrails

These are projection theorems only.  They do not add:

- transport or propagation,
- list-wide coverage,
- aggregation,
- canonical witness selection,
- overlap repair,
- convergence or Collatz termination.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```

