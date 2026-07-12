# Report: petal-249

## Goal

Lift the refined failure-resolution split to `SourcePressureSortedFailureState`.

## Implemented

Added in `DkMath.Collatz.PetalBridge.PressureState`:

```lean
theorem sourcePressureSortedFailureState_to_orientedNeighborDiagnostic_or_pairOverlap
```

This theorem composes:

```lean
sourcePressureSortedFailureState_to_failureResolutionState
sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_pairOverlap
```

and exposes the sorted-failure entry point directly as:

```text
SortedFailureState L
  -> OrientedNeighborDiagnosticState L W W'
   OR
     AdjacentPairInList L A B
     + PairOverlapObstruction A B
```

## Automaton Reading

The state chain now has a sharper public exit from sorted failure:

```text
S -> R -> D ∨ PO
```

where:

- `S` is sorted failure,
- `R` is failure resolution,
- `D` is an oriented neighbor diagnostic,
- `PO` is a concrete pair-level overlap obstruction.

This gives callers a direct theorem from the sorted-failure surface without
manually stepping through the intermediate resolution state.

## Guardrails

This is only a state-lift theorem.  It does not add:

- overlap repair,
- canonical obstructing-pair selection,
- global coverage,
- aggregation over all adjacent pairs,
- transport or propagation,
- convergence or Collatz termination.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```

