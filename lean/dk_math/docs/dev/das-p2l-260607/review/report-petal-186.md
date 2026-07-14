# report-petal-186

Date: 2026-07-06

## Scope

Checkpoint 186 adds a length-three decomposition for the bundled recovered
accounted-family diagnostic carrier in
`DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis`.

The new surface is intentionally bounded.  It only analyzes the explicit
three-witness list `[W1, W2, W3]`.  The result says that a diagnostic is either
located at the head pair `[W1, W2]`, or it is already a diagnostic in the tail
list `[W2, W3]`.

This is a local decomposition theorem, not a global search or coverage theorem.

## Adjacent-pair decomposition

Added:

```lean
theorem
  SourcePressureLocalIslandWitnessAdjacentPairInList.three_head_or_tail
```

For the explicit list `[W1, W2, W3]`, an adjacent-pair address decomposes as:

```lean
(A = W1 ∧ B = W2) ∨
  SourcePressureLocalIslandWitnessAdjacentPairInList [W2, W3] A B
```

This is the raw address-level splitter.  It does not claim uniqueness beyond
what the explicit list structure gives.

## Diagnostic decomposition

Added:

```lean
theorem
  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_head_or_tail
```

For a bundled diagnostic on `[W1, W2, W3]`, the diagnostic is either:

- the head reversed pair, witnessed by
  `SourcePressureLocalIslandWitnessBefore W2 W1`; or
- a bundled diagnostic on the tail `[W2, W3]`.

The head case exposes the pair-local recovered-family facts attached to the
stored diagnostic:

```lean
sourcePressureAccountedIntervalFamilyOfPair W1 W2
```

with its sum bound, strict negativity, and length witness.

## Iff form

Added:

```lean
theorem
  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_iff_head_or_tail
```

This packages the constructor and extractor into an iff form:

```lean
Diagnostic [W1, W2, W3] ↔
  HeadPairDiagnostic W1 W2 ∨ Diagnostic [W2, W3]
```

The reverse direction constructs the head case directly from the existing
reversed-pair accounted-family theorems.  The tail case is lifted with
`of_tail`.

## Failure + no-overlap corollary

Added:

```lean
theorem
  sourcePressureLocalIslandWitnessList_failure_three_diagnostic_head_or_tail_of_noAdjacentOverlap
```

For `[W1, W2, W3]`, sorted-before failure plus the named no-adjacent-overlap
predicate yields the same head-or-tail diagnostic alternative.  This is the
consumer-facing version of the bundled decomposition.

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
three-element explicit list into a head pair or the already-existing
two-element tail diagnostic layer.

## Verification

Commands run:

```text
lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
lake build DkMath.Collatz.PetalBridge.PressureAccounting
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b" DkMath/Collatz/PetalBridge/PressureAccounting.lean DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
git diff --check
```

Results:

- all listed `lake build` commands completed successfully;
- the targeted `rg` no-sorry check returned no matches;
- `git diff --check` passed.

Known unrelated warning still appears during builds:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

This checkpoint did not modify that file.

## File sizes

```text
  1621 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
  1391 lean/dk_math/DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
  1896 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
  4908 total
```

## Next inference

The three-element head-or-tail form is now available as a small bounded
diagnostic normal form.  The next natural extension is not an arbitrary-list
claim.  A safer next step is a length-four theorem that decomposes
`[W1, W2, W3, W4]` into either the head pair or the already-proved
three-element tail.  This keeps the proof chain inductive and explicit while
avoiding global coverage claims.
