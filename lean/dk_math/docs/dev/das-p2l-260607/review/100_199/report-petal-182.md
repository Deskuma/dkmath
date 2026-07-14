# report-petal-182

Date: 2026-07-06

## Scope

This checkpoint continues the pair-local pressure accounting surface in
`DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis`.

The requested target was to expose two already-known structural facts of the
recovered adjacent accounted family:

- the listed recovered budget is strictly negative;
- the accounted interval family built from the recovered pair has length `2`.

No global coverage, maximality, uniqueness, sorting, first-diagnosis,
enumeration, union accounting, overlap repair, or Collatz convergence claim is
introduced.

## Existing facts used

The implementation reuses the reversed-pair accounted family facts from
`PressureLocalWitnessObstruction.lean`:

- `sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_length`
- `sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_items`
- `sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_le_neg_two`
- `sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg`

For this checkpoint, the direct dependencies are:

- `_sum_neg` for strict negativity;
- `_length` for the length-two projection.

## Implemented theorem surface

Added carrier-level projections:

```lean
theorem
    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.exists_accountedFamily_sum_neg
```

This exposes an adjacent pair `A B`, the reverse-before witness `hrev`, and the
associated reversed-pair accounted family whose listed net drop sum is `< 0`.

```lean
theorem
    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.exists_accountedFamily_length_two
```

This exposes the same pair-local family and records that its explicit
`items.length = 2`.

Added consumer wrappers:

```lean
theorem
    sourcePressureLocalIslandWitnessList_failure_exists_accountedFamily_sum_neg_of_noAdjacentOverlap
```

This combines sorted-before failure with the named no-adjacent-overlap
predicate and returns a strictly negative recovered accounted family.

```lean
theorem
    sourcePressureLocalIslandWitnessList_failure_exists_accountedFamily_sum_neg_of_no_overlap
```

This is the raw-negation compatibility wrapper for callers that still hold
`¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L`.

## Mathematical reading

The recovered family is still a single adjacent-pair artifact.  The theorem
surface now lets downstream callers read both:

```text
there exists a recovered adjacent pair,
and its explicit two-item accounted family has negative total net drop.
```

This is intentionally weaker than any list-wide accounting theorem.  The
result says that one local failure can be converted into one local recovered
budget witness, not that all local failures have been globally reconciled.

## File-size check

Current line counts:

```text
1046 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
1391 lean/dk_math/DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
1896 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
```

`PressureAdjacentDiagnosis.lean` remains below the 2000-line local watch limit.

## Verification

Targeted builds run before this report:

```text
lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
lake build DkMath.Collatz.PetalBridge.PressureAccounting
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
```

All completed successfully.

No-sorry check:

```text
rg -n "\bsorry\b" \
  DkMath/Collatz/PetalBridge/PressureAccounting.lean \
  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
```

Result: no matches.  `rg` exited with code `1`, which is the expected
no-match result.

Whitespace check:

```text
git diff --check
```

Result: passed.

## Next inference

The next useful step is probably not aggregation yet.  The API now has:

1. existence of a recovered adjacent accounted family;
2. strict negativity of that family;
3. length-two structure of that family.

The next safe local theorem would be a named consumer that bundles these as one
pair-local diagnostic record, if repeated downstream destructuring becomes
noisy.  That should still avoid list-wide union accounting unless a separate
disjointness or coverage hypothesis is introduced.
