# report-petal-184

Date: 2026-07-06

## Scope

Checkpoint 184 adds basic list-structure API for the bundled recovered
accounted-family diagnostic carrier in
`DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis`.

The diagnostic remains a carrier for one recovered adjacent pair and its
pair-local accounted family.  This checkpoint only makes that carrier easier to
move through explicit list syntax.

## Implemented theorem surface

Added empty-list impossibility:

```lean
theorem
  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.nil_false
```

This follows by unpacking the diagnostic and using the fact that the empty list
has no adjacent pair address.

Added singleton impossibility:

```lean
theorem
  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.singleton_false
```

This similarly reduces to the existing singleton adjacent-pair impossibility.

Added tail lift:

```lean
theorem
  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail
```

This transports a diagnostic from `W2 :: rest` to `W1 :: W2 :: rest`.

The lifted diagnostic is the same pair-local family:

- same recovered pair `A B`;
- same reversed-before witness `hrev`;
- same budget `≤ -2`;
- same strict negativity `< 0`;
- same `items.length = 2`.

Only the list address changes, via
`SourcePressureLocalIslandWitnessAdjacentPairInList.tail`.

Added bounded tail-composition helpers:

```lean
theorem
  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail_tail

theorem
  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail_tail_tail
```

These are small convenience compositions.  No arbitrary recursive lift was
introduced.

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
- a list-wide accounted interval union;
- disjointness between multiple recovered families.

Recovered budgets remain pair-local.

## File-size check

Current line counts:

```text
1356 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
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

This warning is outside the checkpoint scope and was not modified.

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

The diagnostic now has the same basic syntactic mobility as the older adjacent
diagnosis carrier.  A safe next step is to add bounded negative facts for short
lists, such as proving that length two is the first possible carrier shape only
when an explicit recovered adjacent pair is supplied.  That should still stay
away from arbitrary enumeration or global accounting.
