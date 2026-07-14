# Report Petal 190

## Checkpoint

Checkpoint 190 extended the bounded diagnostic decomposition layer to the
explicit five-witness list case.

Primary file:

- `DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean`

No other Lean source file was changed.

## Implemented

### Adjacent-pair length-five head-or-tail theorem

Added:

```lean
theorem SourcePressureLocalIslandWitnessAdjacentPairInList.five_head_or_tail
```

For an adjacent-pair address in `[W1, W2, W3, W4, W5]`, this theorem says the
address is either the head pair `W1, W2` or an adjacent-pair address in the
tail `[W2, W3, W4, W5]`.

This is only the bounded five-element address decomposition.

### Diagnostic length-five head-or-tail theorem

Added:

```lean
theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.five_head_or_tail
```

For a recovered adjacent accounted-family diagnostic on
`[W1, W2, W3, W4, W5]`, this theorem returns either:

- `SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic W1 W2`;
- or a diagnostic on the tail `[W2, W3, W4, W5]`.

The head branch uses the named pair-local predicate from checkpoint 189 instead
of repeating the long recovered-family expression.

### Compact length-five iff theorem

Added:

```lean
theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.five_iff_pairDiagnostic_or_tail
```

This is the iff form of the one-step five-element decomposition:

```text
diagnostic [W1, W2, W3, W4, W5]
  iff
pair diagnostic W1 W2
  or
diagnostic [W2, W3, W4, W5]
```

The reverse direction builds the head-pair diagnostic directly with `of_pair`
or lifts the tail diagnostic with `of_tail`.

### Failure + noAdjacentOverlap consumer wrapper

Added:

```lean
theorem sourcePressureLocalIslandWitnessList_failure_five_pairDiagnostic_or_tail_of_noAdjacentOverlap
```

This combines the existing failure plus no-adjacent-overlap theorem with the new
five-element decomposition.

## Guardrails

This checkpoint is only a five-element explicit-list bounded decomposition.

It did not introduce:

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

Recovered budgets remain pair-local, and the new theorem surface keeps the same
head-pair-or-tail shape used by the existing three/four bounded API.

## File Size Watch

Current line counts:

```text
   702 lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
  1356 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
  1391 lean/dk_math/DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
  1896 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
  5345 total
```

`PressureDiagnosticDecomposition.lean` remains well below the 2,000-line split
threshold.  No refactor was needed in this checkpoint.

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

The bounded chain now reaches five elements with the stable shape:

```text
head pair branch = named pair-local diagnostic
tail branch = remaining bounded diagnostic
```

The next safe step would be another bounded theorem only if a concrete consumer
needs it.  A general arbitrary-list decomposition should remain a separate
design checkpoint because it would require a clear policy for canonical choice,
enumeration, or list recursion without overclaiming coverage.
