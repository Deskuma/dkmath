# Report Petal 191

## Checkpoint

Checkpoint 191 normalized the explicit five-witness diagnostic into a fixed
finite disjunction of adjacent pair diagnostics.

Primary file:

- `DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean`

No other Lean source file was changed.

## Implemented

### Optional three/four pair-cases wrappers

Added:

```lean
theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_pairDiagnostic_cases
theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_pairDiagnostic_cases
```

These are bounded helper normalizations:

```text
Diagnostic [W1, W2, W3]
  -> PairDiagnostic W1 W2 or PairDiagnostic W2 W3

Diagnostic [W1, W2, W3, W4]
  -> PairDiagnostic W1 W2 or PairDiagnostic W2 W3 or PairDiagnostic W3 W4
```

They are fixed-list wrappers only.  They do not classify arbitrary lists.

### Five-to-pairs theorem

Added:

```lean
theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.five_pairDiagnostic_cases
```

This expands:

```text
Diagnostic [W1, W2, W3, W4, W5]
```

into the right-associated finite disjunction:

```text
PairDiagnostic W1 W2
or PairDiagnostic W2 W3
or PairDiagnostic W3 W4
or PairDiagnostic W4 W5
```

The proof uses the one-step five head-or-tail theorem from checkpoint 190, then
the four/three/two bounded normalizations.

### Five iff theorem

Added:

```lean
theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.five_iff_pairDiagnostic_cases
```

This gives the iff form for the fixed five-element list.

The reverse direction builds the diagnostic directly from the selected bounded
adjacent-pair address:

- `W1,W2`: head address;
- `W2,W3`: one tail step then head;
- `W3,W4`: two tail steps then head;
- `W4,W5`: three tail steps then head.

This avoided noisy tail-lift bookkeeping and kept the construction explicitly
bounded.

### Failure + noAdjacentOverlap consumer theorem

Added:

```lean
theorem sourcePressureLocalIslandWitnessList_failure_five_pairDiagnostic_cases_of_noAdjacentOverlap
```

This composes the existing failure plus no-adjacent-overlap diagnostic theorem
with `five_pairDiagnostic_cases`.

## Guardrails

This checkpoint is only a fixed five-element finite disjunction.

It did not introduce:

- arbitrary-list decomposition;
- arbitrary-list recursion;
- aggregation over multiple recovered diagnostics;
- list-wide interval union accounting;
- coverage;
- maximality;
- uniqueness for arbitrary lists;
- sorting theorems;
- canonical first diagnosis for arbitrary lists;
- diagnostic enumeration beyond this fixed finite disjunction;
- overlap repair;
- disjointness between multiple recovered families;
- Collatz convergence.

Recovered budgets remain pair-local.  The theorem only says that, if the
five-element list has a recovered adjacent accounted-family diagnostic, then
one of the four explicit adjacent pairs carries the named pair-local diagnostic.

## File Size Watch

Current line counts:

```text
   879 lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
  1356 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
  1391 lean/dk_math/DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
  1896 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
  5522 total
```

`PressureDiagnosticDecomposition.lean` remains below the 2,000-line split
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

The bounded diagnostic layer now has two views for five elements:

```text
one-step view:
  head pair or tail diagnostic

fully opened view:
  one of the four adjacent pair diagnostics
```

This is enough for fixed-size consumers that need a concrete adjacent pair
without introducing arbitrary-list machinery.  A future general theorem should
remain a separate design checkpoint because it would need a precise policy for
list recursion, canonical choice, and non-overclaiming.
