# Report Petal 193

## Checkpoint

Checkpoint 193 audited the first downstream use site for the bounded
pair-cases API added in checkpoints 191 and 192.

This was an audit-only checkpoint.  No Lean source change was made for cp193.

Primary inspected files:

- `DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean`
- `DkMath/Collatz/PetalBridge/PressureFrontier.lean`
- `DkMath/Collatz/PetalBridge/PressureAccounting.lean`
- `DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean`
- `DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean`

## Search Patterns

Searched for:

```text
SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction
sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
sourcePressureLocalIslandWitnessList_failure_three_diagnostic_head_or_tail_of_noAdjacentOverlap
sourcePressureLocalIslandWitnessList_failure_four_diagnostic_head_or_tail_of_noAdjacentOverlap
sourcePressureLocalIslandWitnessList_failure_five_pairDiagnostic_or_tail_of_noAdjacentOverlap
HasAdjacentDiagnosis
RecoveredAdjacentAccountedFamilyDiagnostic
```

Also checked whether the compact bounded API was already used outside
`PressureDiagnosticDecomposition.lean`:

```text
three_iff_pairDiagnostic_cases
four_iff_pairDiagnostic_cases
five_iff_pairDiagnostic_cases
sourcePressureLocalIslandWitnessList_failure_two_pairDiagnostic_cases_of_noAdjacentOverlap
sourcePressureLocalIslandWitnessList_failure_three_pairDiagnostic_cases_of_noAdjacentOverlap
sourcePressureLocalIslandWitnessList_failure_four_pairDiagnostic_cases_of_noAdjacentOverlap
sourcePressureLocalIslandWitnessList_failure_five_pairDiagnostic_cases_of_noAdjacentOverlap
```

## Audit Result

No direct downstream proof replacement was found.

The compact pair-cases API currently appears only in
`PressureDiagnosticDecomposition.lean`.  The other inspected modules provide
earlier layers:

- `PressureAccounting.lean`: interval-family and pair-local accounting tools;
- `PressureLocalWitnessObstruction.lean`: sorted-before failure and local
  obstruction tools;
- `PressureAdjacentDiagnosis.lean`: adjacent diagnosis, no-overlap, and
  recovered accounted-family carriers;
- `PressureFrontier.lean`: pressure frontier layer.

The most relevant downstream-looking fixed-length theorems are in
`PressureAdjacentDiagnosis.lean`, for example:

```lean
theorem sourcePressureLocalIslandWitnessList_failure_three_hasAdjacentDiagnosis
theorem sourcePressureLocalIslandWitnessList_failure_four_hasAdjacentDiagnosis
theorem sourcePressureLocalIslandWitnessList_failure_five_hasAdjacentDiagnosis
```

However, these theorems produce `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis`
from positive length assumptions and sorted-before failure.  They do not assume
`SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction`, and
their conclusion is a diagnosis carrier, not the recovered pair-local
accounted-family diagnostic exposed by the compact pair-cases API.

Therefore replacing their internals with the new pair-cases API would either:

- add a new no-adjacent-overlap assumption;
- change the theorem's conclusion;
- or move across layer boundaries from diagnosis generation to recovered
  accounted-family decomposition.

That would not be a statement-preserving refactor.

## API Readiness

The current bounded pair-cases API is ready for future concrete consumers.

The most useful future caller shape is expected to be:

```text
fixed list length 2..5
+ sorted-before failure
+ no-adjacent-overlap
-> explicit adjacent pair-local recovered accounted-family diagnostic
```

That caller can now use one of:

```lean
sourcePressureLocalIslandWitnessList_failure_two_pairDiagnostic_cases_of_noAdjacentOverlap
sourcePressureLocalIslandWitnessList_failure_three_pairDiagnostic_cases_of_noAdjacentOverlap
sourcePressureLocalIslandWitnessList_failure_four_pairDiagnostic_cases_of_noAdjacentOverlap
sourcePressureLocalIslandWitnessList_failure_five_pairDiagnostic_cases_of_noAdjacentOverlap
```

No extra wrapper was added because the existing length-five theorem is already
the consumer-friendly form requested by the checkpoint.

## Guardrails

This checkpoint introduced no new mathematical strength.

It did not introduce:

- length-six decomposition;
- arbitrary-list decomposition;
- arbitrary-list recursion;
- aggregation over multiple recovered diagnostics;
- list-wide interval union accounting;
- coverage;
- maximality;
- uniqueness for arbitrary lists;
- sorting theorems;
- canonical first diagnosis for arbitrary lists;
- diagnostic enumeration beyond fixed finite disjunctions;
- overlap repair;
- disjointness between multiple recovered families;
- Collatz convergence.

The audit preserves the current policy: bounded pair-cases are explicit
finite windows only, and recovered budgets remain pair-local.

## File Size Watch

Line counts at the audit point:

```text
  1027 lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
  1356 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
  1391 lean/dk_math/DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
  1896 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
  1517 lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
  7187 total
```

No file crossed the 2,000-line split threshold during this checkpoint.

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

The next implementation should remain consumer-driven.

Good candidates are:

- a concrete theorem in a later pressure module that already has both
  sorted-before failure and no-adjacent-overlap hypotheses;
- a fixed-size recovered-accounting consumer for length five or smaller;
- or a new small theorem that explicitly states the missing bridge between
  adjacent diagnosis and recovered accounted-family diagnostics, if the extra
  no-overlap branch is already naturally available.

Do not add length six until an actual downstream caller asks for it.
