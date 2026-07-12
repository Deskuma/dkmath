# Report: petal-247

## Goal

Connect:

```text
SourcePressureFailureResolutionState
  -> exists SourcePressureOrientedNeighborDiagnosticState
   ∨ SourcePressureAdjacentOverlapState
```

## Result

Implemented successfully.

Updated file:

```text
lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
```

Added theorem:

```lean
theorem sourcePressureFailureResolutionState_to_orientedNeighborDiagnostic_or_overlapState
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureFailureResolutionState L) :
    (∃ W W',
      SourcePressureOrientedNeighborDiagnosticState L W W') ∨
      SourcePressureAdjacentOverlapState L
```

## Proof Chain

Used:

```lean
sourcePressureFailureResolutionState_cases
sourcePressureRecoveredAdjacentState_to_exists_orientedNeighborDiagnosticState
```

The split is:

```text
FailureResolutionState
  -> RecoveredAdjacentState
   ∨ AdjacentOverlapState
```

Recovered branch:

```text
RecoveredAdjacentState
  -> exists OrientedNeighborDiagnosticState
```

Overlap branch:

```text
AdjacentOverlapState
```

## Automaton Reading

The mnemonic transition is now:

```text
R
  -> D
   ∨ O
```

where:

```text
R = failure resolution
D = oriented neighbor diagnostic
O = adjacent overlap obstruction
```

This is a useful checkpoint because the recovered branch no longer stops at
pair-local recovered accounting; it now reaches the Beam-facing oriented
diagnostic state.

## Guardrails

No theorem added:

- overlap repair;
- canonical pair selection;
- list-wide coverage;
- aggregation;
- transport;
- propagation;
- Collatz convergence.

The overlap branch remains an explicit obstruction state.

## Verification

Commands run from:

```text
lean/dk_math
```

Passed:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```
