# Report: petal-257

## Goal

Extract address-level comparison facts from
`SourcePressureLocalIslandWitnessBefore`, then expose the strongest direct
numeric comparison available for a sorted oriented neighbor box.

## Investigation

The witness-level order is definitionally the address-level order:

```lean
SourcePressureLocalIslandWitnessBefore W W'
```

unfolds to:

```lean
SourcePressureIntervalPulseAddressBefore
  (sourcePressureIntervalPulseAddress_of_localIslandWitness W)
  (sourcePressureIntervalPulseAddress_of_localIslandWitness W')
```

The address-level order itself is:

```lean
A.start + A.len <= B.start
```

For local-island witnesses, the converted interval-pulse address is a singleton.
Existing coordinate lemmas give:

```lean
(sourcePressureIntervalPulseAddress_of_localIslandWitness W).start = W.val
(sourcePressureIntervalPulseAddress_of_localIslandWitness W).start
  + (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1
  = W.val
```

Therefore the sorted box comparison can be pushed all the way to:

```lean
W.val < W'.val
```

## Implemented

Added in `DkMath.Collatz.PetalBridge.PressureState`:

```lean
theorem SourcePressureOrientedNeighborBoxState.addressBefore_of_sorted
theorem SourcePressureOrientedNeighborBoxState.rightEdge_lt_start_of_sorted
theorem SourcePressureOrientedNeighborBoxState.rightEdge_le_start_of_sorted
theorem SourcePressureOrientedNeighborBoxState.val_lt_of_sorted
theorem SourcePressureOrientedNeighborBoxState.val_le_of_sorted
```

## Meaning

The comparison chain is now available as a box-facing API:

```text
Box(W,W')
  + SourcePressureLocalIslandWitnessListSortedBefore L
  -> SourcePressureLocalIslandWitnessBefore W W'
  -> address-before between singleton interval-pulse addresses
  -> right-edge(W) < start(W')
  -> W.val < W'.val
```

This is the first explicit numeric/depth comparison extracted from the
two-endpoint box state.

## Guardrails

The new `val_lt_of_sorted` theorem is still local:

* it depends on the explicit oriented neighbor box;
* it depends on sortedness of the enclosing witness list;
* it does not sort arbitrary lists;
* it does not assert global coverage of local islands;
* it does not propagate the comparison beyond the two endpoints;
* it does not prove convergence.

The proof succeeds because local-island witnesses generate singleton
interval-pulse addresses.  For a future non-singleton address carrier, the
strong direct comparison would remain the address-level
`rightEdge < start`, not necessarily a native `val` comparison.

## Verification

Commands run from `lean/dk_math`:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
```

Both builds completed successfully.

`git diff --check` is run as the final whitespace gate for this checkpoint.

## Next Branch Prediction

The natural next branch is to use `val_lt_of_sorted` in pair-comparison or
neighbor-exclusion statements.

Candidate directions:

```text
Box(W,W') + sorted(L)
  -> W.val < W'.val
  -> W.val != W'.val
```

and, if useful for downstream automation:

```text
Box(W,W') + sorted(L)
  -> not reverse address-before
  -> not reverse box ordering
```

The second direction should be added only if a caller needs a negative
orientation fact.  The clean positive fact is now `val_lt_of_sorted`.
