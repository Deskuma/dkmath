# report-petal-183

Date: 2026-07-06

## Scope

Checkpoint 183 adds a bundled pair-local diagnostic carrier in
`DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis`.

The goal was not to strengthen the accounting model globally.  The new surface
only packages facts already available for one recovered adjacent reversed pair:

- adjacent pair membership in the explicit list;
- reversed-before witness;
- the recovered pair-local accounted family;
- budget `≤ -2`;
- strict negative budget `< 0`;
- `items.length = 2`.

## Implemented carrier

Added:

```lean
def SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
```

This carrier is intentionally redundant.  The lower-level recovered carrier
already stores `≤ -2`, and cp182 exposed `< 0` and `items.length = 2`.  The new
diagnostic bundles those facts so downstream callers can destruct one carrier
instead of repeatedly calling separate projections.

The definition remains one-pair only.  It does not aggregate recovered pairs or
build a list-wide accounted interval union.

## Constructors and conversions

Added:

```lean
theorem
  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
```

This constructs the diagnostic from explicit adjacent-pair evidence and the
three pair-local facts.

Added:

```lean
theorem
  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.toDiagnostic
```

This upgrades the existing recovered carrier to the bundled diagnostic.  The
proof reuses the existing reversed-pair family facts:

- `sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg`
- `sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_length`

Added:

```lean
theorem
  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.toRecoveredAdjacentAccountedFamily
```

This forgets the extra diagnostic fields and returns the existing lower-level
recovered carrier.

## Consumer theorem

Added:

```lean
theorem
  sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
```

This packages the failure + named no-adjacent-overlap branch directly into the
new diagnostic carrier.

Also added the raw-negation compatibility wrapper:

```lean
theorem
  sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_no_overlap
```

## Additional projections

Added lightweight projections from the diagnostic:

```lean
theorem
  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_pair

theorem
  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_accountedFamily_sum_neg

theorem
  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_accountedFamily_length_two
```

These are convenience projections only.  They do not assert uniqueness, choose a
canonical diagnosis, or enumerate every possible diagnostic.

## Guardrails preserved

This checkpoint did not introduce:

- global local-island coverage;
- maximality;
- uniqueness;
- prefix behavior;
- arbitrary list sorting;
- canonical first diagnosis;
- enumeration of all diagnoses;
- union accounting;
- overlap repair;
- Collatz convergence;
- aggregation of multiple recovered pairs;
- disjointness between multiple recovered families.

Recovered budgets remain pair-local.

## File-size check

Current line counts:

```text
1270 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
1391 lean/dk_math/DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
1896 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
```

`PressureAdjacentDiagnosis.lean` remains below the 2000-line split threshold.

## Verification

Builds:

```text
lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
lake build DkMath.Collatz.PetalBridge.PressureAccounting
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
```

All completed successfully.

Known unrelated warning:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

This is outside the checkpoint scope and was not modified.

No-sorry check on the targeted pressure files:

```text
rg -n "\bsorry\b" \
  DkMath/Collatz/PetalBridge/PressureAccounting.lean \
  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
```

Result: no matches.  `rg` exited with code `1`, which is the expected no-match
result.

Whitespace check:

```text
git diff --check
```

Result: passed.

## Next inference

The new diagnostic carrier is now the clean consumer surface for one recovered
adjacent local accounting witness.  The next safe step is to use this carrier
where repeated destructuring appears, or to add a small negative example showing
that short lists still cannot produce the diagnostic.  Aggregation should remain
blocked until an explicit disjointness or coverage hypothesis is available.
