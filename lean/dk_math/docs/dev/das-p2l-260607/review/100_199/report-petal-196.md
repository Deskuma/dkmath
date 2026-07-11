# report-petal-196

## Checkpoint

Checkpoint 196 closes the arbitrary-list branch split requested by the
reviewer.

The implemented theorem is:

```lean
theorem
    sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_or_adjacentOverlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L) :
    (∃ A B,
      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
        SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
          A B) ∨
      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
```

## Implementation

The theorem was added to:

```text
DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
```

It is a named-surface wrapper over the existing arbitrary-list theorem:

```lean
sourcePressureLocalIslandWitnessList_failure_exists_recovered_or_overlap
```

The recovered branch is repackaged into the named pair-local predicate
`SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic`
using:

```lean
SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic.of_before
```

The existing recovered budget witness is intentionally not strengthened.  The
new theorem only exposes the already available branch split in the diagnostic
vocabulary used downstream.

## Guardrails

This theorem does not assume no-overlap.  The overlap obstruction is preserved
as the right-hand branch.

It does not claim:

- global coverage,
- canonical diagnosis,
- enumeration of all failing adjacent pairs,
- aggregation of recovered families,
- overlap repair,
- disjointness between recovered families,
- Collatz convergence.

The theorem remains an arbitrary-list existential projection: under sorted-
before failure, either some adjacent pair has the named recovered diagnostic,
or an adjacent overlap obstruction is present.

## Verification

Commands run from `lean/dk_math`:

```text
lake build DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
lake build DkMath.Collatz.PetalBridge.PressureAccounting
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
```

All builds passed.

No-sorry check over the requested pressure files:

```text
rg -n "\bsorry\b|admit" \
  DkMath/Collatz/PetalBridge/PressureAccounting.lean \
  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean \
  DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
```

Result: no matches.

The known unrelated warning remains:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

This was not touched.

Line counts after the checkpoint:

```text
  1130 DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
  1356 DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
  1391 DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
  1896 DkMath/Collatz/PetalBridge/PressureAccounting.lean
  1517 DkMath/Collatz/PetalBridge/PressureFrontier.lean
  7290 total
```

## Next inference

The next natural consumer is a small downstream theorem that combines this
branch split with a no-overlap assumption only at the usage point.  That is
already essentially present as the existing no-overlap consumer:

```lean
sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_noAdjacentOverlap
```

So the current API now has the intended two-stage shape:

1. branch split without no-overlap,
2. recovered diagnostic extraction with no-overlap.

This keeps the overlap obstruction visible instead of silently discarding it.
