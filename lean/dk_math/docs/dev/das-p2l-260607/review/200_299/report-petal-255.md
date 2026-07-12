# Report: petal-255

## Goal

Extract the ordered before/value relation from
`SourcePressureOrientedNeighborBoxState`.

## Investigation Result

The available stored relation is:

```lean
SourcePressureLocalIslandWitnessAdjacentPairInList L W W'
```

This relation means that `W` and `W'` occur as an ordered neighboring pair in
the explicit witness list `L`.

It does not imply either of the stronger relations:

```lean
SourcePressureLocalIslandWitnessBefore W W'
W.val < W'.val
```

The reason is structural: `AdjacentPairInList` is a list-address relation only.
It records ordered neighboring positions in `L`, but it does not say that `L`
is sorted by pulse-address order or by numeric depth.

## Implemented

Added in `DkMath.Collatz.PetalBridge.PressureState`:

```lean
theorem SourcePressureOrientedNeighborBoxState.orderedAdjacentPairInList
theorem SourcePressureOrientedNeighborBoxState.left_mem
theorem SourcePressureOrientedNeighborBoxState.right_mem
```

The new comparison-facing projection is intentionally an alias of the existing
box adjacent-pair projection:

```text
Box(W,W') -> AdjacentPairInList L W W'
```

The membership projections expose:

```text
Box(W,W') -> W  in L
Box(W,W') -> W' in L
```

## Code Comment

Added a source-level note explaining why `Before` and `W.val < W'.val` are not
derived here.  Future comparison theorems should add an explicit sortedness or
address-order hypothesis before attempting to prove those stronger relations.

## Next Direction

The next comparison layer should likely introduce one of:

```text
AdjacentPairInList L W W'
+ list sorted by witness address
-> SourcePressureLocalIslandWitnessBefore W W'
```

or:

```text
AdjacentPairInList L W W'
+ list sorted by W.val
-> W.val < W'.val
```

This keeps list adjacency separate from mathematical address/depth order.

## Guardrails

This checkpoint does not add:

- witness-level `Before`,
- numeric depth comparison,
- sortedness assumptions,
- transport or propagation,
- coverage or aggregation,
- convergence or Collatz termination.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```

