# Report Petal 195

## Checkpoint

Checkpoint 195 added the main-root existential projection from a list-level
recovered diagnostic carrier to the named pair-local recovered diagnostic
predicate.

Primary file:

- `DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean`

No supporting Lean file was modified.

## Implemented

### List carrier projection to named pair diagnostic

Added:

```lean
theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_pairDiagnostic
```

Shape:

```lean
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic L
  ->
∃ A B,
  SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
    SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic A B
```

This theorem uses the existing `h.exists_pair` projection from the bundled
list-level diagnostic carrier and repackages the stored fields:

```text
hin
hrev
hbudget
hneg
hlen
```

into the named pair-local predicate:

```lean
SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic A B
```

No new mathematical information is introduced.

### Named noAdjacentOverlap consumer

Added:

```lean
theorem sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_noAdjacentOverlap
```

Shape:

```lean
SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L
  ->
SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction L
  ->
∃ A B,
  SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
    SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic A B
```

This composes the existing bridge:

```lean
sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
```

with the new `.exists_pairDiagnostic` projection.

### Raw no-overlap compatibility wrapper

Added:

```lean
theorem sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_no_overlap
```

This is the same existential named pair-diagnostic result, but for callers that
still carry no-overlap as:

```lean
¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
```

It composes the existing raw bridge:

```lean
sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_no_overlap
```

with `.exists_pairDiagnostic`.

## Meaning

The checkpoint completes the thin arbitrary-list existential consumer surface:

```text
fixed length 2..5:
  finite pair-cases disjunction API

arbitrary explicit list:
  existential named pairDiagnostic API
```

The arbitrary-list theorem is existential only.  It says that the already
recovered carrier contains some adjacent pair whose pair-local recovered
accounted-family diagnostic can be named directly.

## Guardrails

This checkpoint only repackages an already stored recovered diagnostic witness.

It did not introduce:

- length-six decomposition;
- arbitrary-list decomposition;
- arbitrary-list recursion;
- canonical first diagnosis for arbitrary lists;
- enumeration of all diagnostics;
- aggregation over multiple recovered diagnostics;
- list-wide interval union accounting;
- coverage;
- maximality;
- uniqueness for arbitrary lists;
- sorting theorems;
- overlap repair;
- disjointness between multiple recovered families;
- Collatz convergence.

In particular, the new existential theorem does not choose a canonical pair,
does not enumerate diagnostics, does not aggregate families, does not repair
overlap, and does not prove coverage.

## File Size Watch

Current line counts:

```text
  1097 lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
  1356 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
  1391 lean/dk_math/DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
  1896 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
  1517 lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
  7257 total
```

`PressureDiagnosticDecomposition.lean` remains below the 2,000-line split
threshold.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
lake build DkMath.Collatz.PetalBridge.PressureAccounting
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
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

The pressure diagnostic layer now has two complementary consumer surfaces:

```text
bounded fixed windows:
  explicit finite disjunction over adjacent pairs

arbitrary explicit list:
  existential named recovered pair diagnostic
```

The next safe move remains consumer-driven.  A later theorem can use the
existential projection when it only needs one recovered pair-local diagnostic,
while fixed small-window callers should continue to use the sharper pair-cases
API.
