# Report: petal-253

## Goal

Lift the refined diagnostic/overlap split from oriented diagnostic state `D` to
the two-endpoint box state.

## Implemented

Added in `DkMath.Collatz.PetalBridge.PressureState`:

```lean
theorem sourcePressureFailureResolutionState_to_orientedNeighborBox_or_pairOverlap
theorem sourcePressureSortedFailureState_to_orientedNeighborBox_or_pairOverlap
theorem sourcePressureBeamSeedState_to_orientedNeighborBox_or_pairOverlap
```

The main split is now:

```text
FailureResolutionState L
  -> OrientedNeighborBoxState L W W'
   OR
     AdjacentPairInList L A B
     + PairOverlapObstruction A B
```

The sorted-failure and Beam-seed versions are thin lifts through the existing
state transitions.

## Proof Shape

The failure-resolution theorem uses:

```lean
sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_pairOverlap
sourcePressureOrientedNeighborDiagnosticState_to_boxState
```

Only the diagnostic branch is strengthened from `D` to the two-endpoint box.
The overlap branch is left as the already-refined concrete pair-level overlap
obstruction.

## Automaton Reading

The state exits are now:

```text
R -> Box ∨ PO
S -> Box ∨ PO
B -> Box ∨ PO
```

where:

- `R` is failure resolution,
- `S` is sorted failure,
- `B` is Beam seed,
- `Box` is the two-endpoint oriented neighbor box,
- `PO` is a concrete pair-level overlap obstruction.

## Guardrails

This checkpoint only packages an already-local diagnostic branch.  It does not
add:

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

