# report-petal-187

Date: 2026-07-06

## Scope

Checkpoint 187 adds a length-four bounded decomposition for the bundled
recovered accounted-family diagnostic carrier in
`DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis`.

The result is local to the explicit witness list `[W1, W2, W3, W4]`.  It says
that a diagnostic is either carried by the head pair `[W1, W2]`, or it already
lives in the tail list `[W2, W3, W4]`.

This is a bounded decomposition theorem, not a global diagnostic search.

## Adjacent-pair decomposition

Added:

```lean
theorem
  SourcePressureLocalIslandWitnessAdjacentPairInList.four_head_or_tail
```

For the explicit list `[W1, W2, W3, W4]`, an adjacent-pair address decomposes
as:

```lean
(A = W1 ∧ B = W2) ∨
  SourcePressureLocalIslandWitnessAdjacentPairInList [W2, W3, W4] A B
```

This is the raw address-level splitter.  It follows the same bounded-list shape
as the previous two- and three-element normal forms.

## Diagnostic decomposition

Added:

```lean
theorem
  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_head_or_tail
```

For a bundled diagnostic on `[W1, W2, W3, W4]`, the diagnostic is either:

- the head reversed pair, witnessed by
  `SourcePressureLocalIslandWitnessBefore W2 W1`; or
- a bundled diagnostic on the tail `[W2, W3, W4]`.

The head case exposes the pair-local recovered-family facts attached to
`sourcePressureAccountedIntervalFamilyOfPair W1 W2`: sum bound, strict
negativity, and length two.

## Iff form

Added:

```lean
theorem
  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_iff_head_or_tail
```

This packages the four-element decomposition into an iff.  The reverse
direction constructs the head-pair diagnostic directly from the reversed-before
witness, or lifts an existing diagnostic from the three-element tail.

## Failure + no-overlap corollary

Added:

```lean
theorem
  sourcePressureLocalIslandWitnessList_failure_four_diagnostic_head_or_tail_of_noAdjacentOverlap
```

For `[W1, W2, W3, W4]`, sorted-before failure plus the named no-adjacent-overlap
predicate yields the same head-or-tail diagnostic alternative.  This is the
consumer-facing version of the bundled decomposition.

## Optional pair enumeration

The fully bounded four-to-pairs corollary was not added in this checkpoint.
It would duplicate a long nested statement and is better deferred until there
is a concrete downstream consumer.  The current head-or-tail form is the more
stable API.

## File-size watch

Current line counts:

```text
  1750 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
  1391 lean/dk_math/DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
  1896 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
  5037 total
```

`PressureAdjacentDiagnosis.lean` is below the 1900-line watch threshold, so this
checkpoint did not start a refactor.  If the next bounded-decomposition layer
pushes the file toward 1900-2000 lines, the next checkpoint should consider
extracting bounded diagnostic decomposition helpers to a new module.

## Guardrails preserved

This checkpoint did not introduce:

- global local-island coverage;
- maximality;
- uniqueness for arbitrary lists;
- prefix behavior;
- arbitrary list sorting;
- canonical first diagnosis for arbitrary lists;
- enumeration of all diagnostics;
- union accounting;
- overlap repair;
- Collatz convergence;
- aggregation of multiple recovered pairs;
- a list-wide accounted interval union;
- disjointness between multiple recovered families.

Recovered budgets remain pair-local.  The new theorem only opens a
four-element explicit list into a head pair or the existing three-element tail
diagnostic layer.

## Verification

Commands run:

```text
lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
lake build DkMath.Collatz.PetalBridge.PressureAccounting
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b" DkMath/Collatz/PetalBridge/PressureAccounting.lean DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
```

Results:

- all listed `lake build` commands completed successfully;
- the targeted `rg` no-sorry check returned no matches.

Known unrelated warning still appears during builds:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

This checkpoint did not modify that file.

## Next inference

The bounded chain now has length two, three, and four forms.  The next natural
step is not arbitrary-list generalization.  A safe next checkpoint is either:

- a consumer-driven theorem that uses the four-element head-or-tail form; or
- a small extraction module for bounded diagnostic decompositions before adding
  a length-five layer.

The second option is preferable if the file-size watch becomes active.
