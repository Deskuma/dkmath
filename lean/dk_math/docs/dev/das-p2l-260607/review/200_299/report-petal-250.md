# Report: petal-250

## Goal

Lift the refined diagnostic/obstruction split to `SourcePressureBeamSeedState`.

## Implemented

Added in `DkMath.Collatz.PetalBridge.PressureState`:

```lean
theorem sourcePressureBeamSeedState_to_orientedNeighborDiagnostic_or_pairOverlap
```

This theorem composes:

```lean
sourcePressureBeamSeedState_to_failureResolutionState
sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_pairOverlap
```

and exposes the Beam-seed entry point directly as:

```text
BeamSeedState L
  -> OrientedNeighborDiagnosticState L W W'
   OR
     AdjacentPairInList L A B
     + PairOverlapObstruction A B
```

## Automaton Reading

The Beam-seed branch now reaches the same pair-refined diagnostic surface as
sorted failure:

```text
B -> R -> D ∨ PO
```

where:

- `B` is Beam seed,
- `R` is failure resolution,
- `D` is an oriented neighbor diagnostic,
- `PO` is a concrete pair-level overlap obstruction.

This lets Beam-facing callers use a single theorem without manually stepping
through the failure-resolution state.

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

