# Report Petal 189

## Checkpoint

Checkpoint 189 was an API-compression pass for the bounded diagnostic
decomposition layer.

Primary file:

- `DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean`

No other Lean source file was changed.

## Implemented

### Named pair-local recovered branch

Added:

```lean
def SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
```

This names the long recovered head-pair branch that was repeated in the
length-two, length-three, and length-four decomposition statements.

The predicate is strictly pair-local to `W1, W2`.  It packages:

- a reversed-before witness `W2` before `W1`;
- the recovered accounted interval family for that reversed pair;
- the existing `sum ≤ -2` budget fact;
- the existing `sum < 0` negativity fact;
- the existing `items.length = 2` fact.

### Constructor

Added:

```lean
theorem SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic.of_before
```

This constructor repackages the already-existing reversed-pair facts:

- `sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_le_neg_two`
- `sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg`
- `sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_length`

No new mathematical strength is introduced.

### Compact decomposition wrappers

Added compact wrappers:

```lean
theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.two_iff_pairDiagnostic
theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pairDiagnostic_two
theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_iff_pairDiagnostic_or_tail
theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_iff_pairDiagnostic_or_tail
```

These are readability wrappers around the existing bounded decomposition API.
They replace the repeated long head branch with the named pair-local predicate.

### Compact consumer wrappers

Added compact failure/no-adjacent-overlap consumer wrappers:

```lean
theorem sourcePressureLocalIslandWitnessList_failure_two_pairDiagnostic_of_noAdjacentOverlap
theorem sourcePressureLocalIslandWitnessList_failure_three_pairDiagnostic_or_tail_of_noAdjacentOverlap
theorem sourcePressureLocalIslandWitnessList_failure_four_pairDiagnostic_or_tail_of_noAdjacentOverlap
```

These expose the same results as the existing long consumer theorems, but with
the head branch expressed using
`SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic`.

## Guardrails

This checkpoint intentionally did not add:

- length-five decomposition;
- arbitrary-list decomposition;
- aggregation over multiple recovered diagnostics;
- list-wide interval union accounting;
- coverage;
- maximality;
- uniqueness for arbitrary lists;
- sorting theorems;
- canonical first diagnosis for arbitrary lists;
- diagnostic enumeration;
- overlap repair;
- disjointness between multiple recovered families;
- Collatz convergence.

The theorem strength is unchanged.  The long recovered head branch was only
given a stable public name.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
lake build DkMath.Collatz.PetalBridge.PressureAccounting
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
git diff --check
```

No-sorry check over the requested pressure files produced no matches:

```text
rg -n "\bsorry\b" \
  DkMath/Collatz/PetalBridge/PressureAccounting.lean \
  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean \
  DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
```

Known unrelated warning still appears during builds:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

That warning is outside this checkpoint and was not modified.

## Next Inference

The bounded diagnostic layer is now easier to extend because the head-pair
branch has a stable name.  If the next checkpoint grows length-five or another
bounded decomposition, it should use the new pair-local predicate immediately
instead of repeating the long branch expression.

The next step should still remain bounded unless a separate design checkpoint
introduces a sound arbitrary-list decomposition policy.
