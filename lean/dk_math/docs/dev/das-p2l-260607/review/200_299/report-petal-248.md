# Report: petal-248

## Goal

Refine `SourcePressureAdjacentOverlapState` from a list-level overlap state into a concrete
pair-level overlap obstruction.

## Implemented

Added in `DkMath.Collatz.PetalBridge.PressureState`:

```lean
theorem sourcePressureAdjacentOverlapState_to_exists_pairOverlapObstruction
```

This theorem turns

```lean
SourcePressureAdjacentOverlapState L
```

into an addressed adjacent pair:

```lean
∃ A B,
  SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
    SourcePressureLocalIslandWitnessPairOverlapObstruction A B
```

It is a thin state-level wrapper over the existing pair extraction theorem:

```lean
exists_adjacentPairInList_pairOverlapObstruction_of_overlapObstruction
```

Also added:

```lean
theorem sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_pairOverlap
```

This refines the previous failure-resolution split from

```text
oriented diagnostic OR list-level overlap state
```

to

```text
oriented diagnostic OR concrete adjacent pair-level overlap obstruction
```

## Automaton Reading

The pressure-state automaton now has a sharper failure-resolution exit:

```text
FailureResolutionState L
  -> OrientedNeighborDiagnosticState L W W'
   OR
     AdjacentPairInList L A B
     + PairOverlapObstruction A B
```

So the mnemonic transition is:

```text
R -> D ∨ PO
```

where:

- `R` is failure resolution,
- `D` is an oriented neighbor diagnostic,
- `PO` is a pair-level overlap obstruction.

This is useful because callers no longer have to stay at the coarse list-overlap
surface when the next argument needs the actual adjacent pair.

## Guardrails

This checkpoint deliberately does not prove any of the following:

- overlap repair,
- canonical obstructing-pair selection,
- global coverage,
- aggregation over all adjacent pairs,
- transport or propagation of diagnostics,
- convergence or Collatz termination.

The theorem only exposes the concrete pair that already exists behind the
list-level overlap obstruction.

## Verification

Passed before this report was written:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```

