# report-petal-197

## Checkpoint

Checkpoint 197 was an audit-only checkpoint.

No Lean theorem was added.  The requested no-overlap consumer already exists,
and the arbitrary-list diagnostic API has the intended two-stage shape.

## Theorems inspected

The branch split without no-overlap is:

```lean
sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_or_adjacentOverlap
```

It states that sorted-before failure gives either:

1. some adjacent pair carrying
   `SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic`,
2. or an adjacent overlap obstruction.

The no-overlap consumer is:

```lean
sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_noAdjacentOverlap
```

It states that sorted-before failure plus
`SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction L`
extracts an existential adjacent pair with the named pair-local recovered
diagnostic.

The consumer is currently implemented through the existing carrier theorem:

```lean
sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
```

and then projects:

```lean
.exists_pairDiagnostic
```

## API shape confirmed

The downstream shape is now:

```text
sorted-before failure
  -> pairDiagnostic-or-adjacentOverlap

sorted-before failure + no-adjacent-overlap
  -> exists pairDiagnostic
```

This is the desired separation:

1. The branch split does not hide overlap and does not require no-overlap.
2. The recovered diagnostic extraction is only claimed once no-overlap is
   supplied.

## Guardrails

No overlap repair was added.

No theorem was added for:

- length-six decomposition,
- arbitrary-list recursive decomposition,
- canonical first diagnosis,
- enumeration of all diagnostics,
- aggregation over multiple recovered diagnostics,
- list-wide interval union accounting,
- coverage,
- maximality,
- uniqueness,
- sorting,
- disjointness between multiple recovered families,
- Collatz convergence.

The present API remains local to explicit adjacent-pair witnesses.

## File-size status

The primary file remains below the 2,000-line refactoring threshold:

```text
  1130 DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
```

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

Result: all builds passed.

No-sorry check over the requested files:

```text
rg -n "\bsorry\b|admit" \
  DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean \
  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean \
  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
  DkMath/Collatz/PetalBridge/PressureAccounting.lean \
  DkMath/Collatz/PetalBridge/PressureFrontier.lean
```

Result: no matches.

`git diff --check` passed.

Known unrelated warning:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

This checkpoint did not touch that file.
