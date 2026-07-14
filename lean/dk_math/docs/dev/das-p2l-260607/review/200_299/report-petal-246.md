# Report: petal-246

## Goal

Connect:

```text
SourcePressureRecoveredAdjacentState
  -> exists SourcePressureOrientedNeighborDiagnosticState
```

## Result

Implemented successfully.

Updated file:

```text
lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
```

Added theorem:

```lean
theorem sourcePressureRecoveredAdjacentState_to_exists_orientedNeighborDiagnosticState
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureRecoveredAdjacentState L) :
    ∃ W W',
      SourcePressureOrientedNeighborDiagnosticState L W W'
```

## Bridge Found

The possible missing bridge was:

```text
PairHasRecoveredAccountedFamilyDiagnostic -> AdjacentDiagnosis
```

This bridge was not missing.

`SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic`
already stores:

```lean
∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
  budget ≤ -2 ∧ negative ∧ length = 2
```

The lower adjacent diagnosis constructor only needs the first two pieces:

```lean
SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered hrev hbudget
```

So the proof path is:

```text
RecoveredAdjacentState L
  -> exists A B, AdjacentPairInList L A B + PairHasRecovered...
  -> AdjacentDiagnosis L A B
  -> OrientedNeighborDiagnosticState L A B
```

## Gap Filled

This fills the recovered-branch version of:

```text
missingAdjacentDiagnosis
```

with opcode reading:

```text
attachAdjacentDiagnosis + attachForwardOrientation
```

It does not fill the general case:

```text
NeighborCandidate alone -> OrientedNeighborDiagnostic
```

That still needs orientation and diagnosis evidence.

## Guardrails

No theorem added:

- canonical pair selection beyond the existential pair already stored;
- list-wide coverage;
- aggregation;
- overlap repair;
- transport;
- propagation;
- Collatz convergence.

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
