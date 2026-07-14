# report-petal-185

Date: 2026-07-06

## Scope

Checkpoint 185 adds a length-two normal form for the bundled recovered
accounted-family diagnostic carrier in
`DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis`.

This is only about the explicit two-witness list `[W1, W2]`.  It does not choose
a canonical diagnostic in longer lists and does not enumerate all diagnostics.

## Adjacent-pair normal form

Added:

```lean
theorem
  SourcePressureLocalIslandWitnessAdjacentPairInList.two_iff_head
```

For a two-element explicit witness list, the only adjacent-pair address is the
head pair:

```lean
SourcePressureLocalIslandWitnessAdjacentPairInList [W1, W2] A B ↔
  A = W1 ∧ B = W2
```

Also added the extractor:

```lean
theorem
  SourcePressureLocalIslandWitnessAdjacentPairInList.two_eq
```

This is a convenience projection used by the diagnostic normal form.

## Diagnostic constructor

Added:

```lean
theorem
  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_two_reversed
```

For `[W1, W2]`, a witness

```lean
SourcePressureLocalIslandWitnessBefore W2 W1
```

directly constructs the bundled diagnostic.  The budget facts are supplied by
the existing reversed-pair accounted-family theorems:

- `sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_le_neg_two`
- `sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg`
- `sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_length`

## Diagnostic extractor

Added:

```lean
theorem
  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_reversed_of_two
```

This extracts the reversed-before witness and the bundled pair-local facts from
a diagnostic on `[W1, W2]`.

The proof uses `two_eq` to normalize the stored adjacent-pair address to
`A = W1` and `B = W2`, then returns the stored reversed-pair family facts.

## Iff form

Added:

```lean
theorem
  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.two_iff
```

This packages the constructor and extractor into a two-element normal-form
equivalence.

The reverse direction uses the existing reversed-pair theorems again through
`of_two_reversed`, so the supplied existential facts do not need to be replayed.

## Failure + no-overlap corollary

Added:

```lean
theorem
  sourcePressureLocalIslandWitnessList_failure_two_exists_reversed_of_noAdjacentOverlap
```

For a two-element list, sorted-before failure plus the named no-adjacent-overlap
predicate yields the reversed-before witness for the only possible adjacent
pair and returns the paired budget facts.

## Guardrails preserved

This checkpoint did not introduce:

- global local-island coverage;
- maximality;
- uniqueness for arbitrary lists;
- prefix behavior;
- arbitrary list sorting;
- canonical first diagnosis for arbitrary lists;
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
1494 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
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

The diagnostic carrier now has a clean minimal two-element normal form:

```text
[W1, W2] with W2 before W1
```

The next safe extension is probably another bounded structural theorem, for
example a length-three decomposition that says a diagnostic on `[W1, W2, W3]`
is either the head-pair normal form or a tail-lifted two-element normal form.
That should still avoid arbitrary enumeration and list-wide accounting.
