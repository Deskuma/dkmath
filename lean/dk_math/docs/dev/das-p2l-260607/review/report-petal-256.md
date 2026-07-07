# Report: petal-256

## Goal

Find or define the sortedness/address-order bridge needed to turn
`SourcePressureLocalIslandWitnessAdjacentPairInList` into witness order or value
order.

## Investigation

The required sortedness invariant already exists:

```lean
SourcePressureLocalIslandWitnessListSortedBefore L
```

This is the witness-list version of address-family sortedness.  It sorts the
local island witnesses after converting them to interval-pulse addresses.

The right target for this checkpoint is also already present:

```lean
SourcePressureLocalIslandWitnessBefore W W'
```

This is stronger and more structural than a raw `W.val < W'.val` target for the
current layer, because it records the address-level ordered non-overlap relation
used by the pressure accounting files.

No existing invariant was found that directly gives `W.val < W'.val` from
adjacency.  This report therefore keeps the new bridge at witness/address order.

## Implemented

Added in `DkMath.Collatz.PetalBridge.PressureState`:

```lean
theorem sourcePressureAdjacentPairInList_before_of_sorted
```

This proves:

```text
SourcePressureLocalIslandWitnessListSortedBefore L
  + SourcePressureLocalIslandWitnessAdjacentPairInList L W W'
  -> SourcePressureLocalIslandWitnessBefore W W'
```

Also added the box-facing projection:

```lean
theorem SourcePressureOrientedNeighborBoxState.before_of_sorted
```

This packages the common caller path:

```text
Box(W,W')
  -> ordered adjacent pair in L
  -> sortedness of L
  -> W before W'
```

## Meaning

The two-endpoint box now has a clean entrance into the comparison layer.

Before this checkpoint, `Box(W,W')` could project its oriented diagnostic and
adjacent-pair data, but it did not have a local theorem that combines that
adjacency with the enclosing list sortedness invariant.

After this checkpoint, downstream pair-comparison work can stay at the
box-facing API:

```lean
hbox.before_of_sorted hsorted
```

## Guardrails

The new theorem does not prove numeric depth comparison:

```lean
W.val < W'.val
```

It also does not add coverage, transport, propagation, convergence, or any
global Collatz claim.  It only connects an explicit adjacent pair in a sorted
witness list to the already-defined witness-level `Before` relation.

## Verification

Commands run from `lean/dk_math`:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
```

Both builds completed successfully.

`git diff --check` is run as the final whitespace gate for this checkpoint.

## Next Branch Prediction

The next natural branch is pair comparison under the `Before` relation.

Candidate direction:

```text
SourcePressureOrientedNeighborBoxState L W W'
  + SourcePressureLocalIslandWitnessListSortedBefore L
  -> SourcePressureLocalIslandWitnessBefore W W'
  -> pair comparison facts usable by the pressure-beam layer
```

If a numeric theorem is needed, the next investigation should inspect whether
`SourcePressureLocalIslandWitnessBefore W W'` already implies a useful value or
address inequality.  If it does not, the smallest bridge should be added at the
`SourcePressureLocalIslandWitnessBefore` layer, not at the box layer.
