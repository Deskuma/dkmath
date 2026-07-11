# Report Petal 192

## Checkpoint

Checkpoint 192 completed the fixed three/four-element pair-cases API for the
bounded pressure diagnostic decomposition layer.

Primary file:

- `DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean`

No other Lean source file was changed.

## Implemented

### Three-element iff pair-cases theorem

Added:

```lean
theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_iff_pairDiagnostic_cases
```

This gives the fixed three-element equivalence:

```text
Diagnostic [W1, W2, W3]
  iff
PairDiagnostic W1 W2 or PairDiagnostic W2 W3
```

The forward direction uses the existing three-element finite decomposition.
The reverse direction builds the list diagnostic directly from the selected
bounded adjacent-pair address:

- `W1,W2`: head address;
- `W2,W3`: one tail step then head.

### Four-element iff pair-cases theorem

Added:

```lean
theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_iff_pairDiagnostic_cases
```

This gives the fixed four-element equivalence:

```text
Diagnostic [W1, W2, W3, W4]
  iff
PairDiagnostic W1 W2
or PairDiagnostic W2 W3
or PairDiagnostic W3 W4
```

The reverse direction again uses explicit bounded addresses:

- `W1,W2`: head address;
- `W2,W3`: one tail step then head;
- `W3,W4`: two tail steps then head.

### Two-element naming alias

Added:

```lean
theorem sourcePressureLocalIslandWitnessList_failure_two_pairDiagnostic_cases_of_noAdjacentOverlap
```

This is a naming-style alias for the existing two-element consumer theorem.
For two witnesses, the fully opened finite pair-cases result is just the
unique head pair.

### Three/four consumer wrappers

Added:

```lean
theorem sourcePressureLocalIslandWitnessList_failure_three_pairDiagnostic_cases_of_noAdjacentOverlap
theorem sourcePressureLocalIslandWitnessList_failure_four_pairDiagnostic_cases_of_noAdjacentOverlap
```

These compose the existing failure plus no-adjacent-overlap diagnostic theorem
with the fixed three/four pair-cases normalizations.

They provide direct consumer-facing results:

```text
failure + noAdjacentOverlap on [W1, W2, W3]
  -> PairDiagnostic W1 W2 or PairDiagnostic W2 W3

failure + noAdjacentOverlap on [W1, W2, W3, W4]
  -> PairDiagnostic W1 W2
     or PairDiagnostic W2 W3
     or PairDiagnostic W3 W4
```

## API Status

The bounded pair-cases API now has matching fixed-length surfaces for
lengths two through five:

```text
2: direct pair diagnostic
3: forward cases, iff cases, failure/noAdjacentOverlap consumer
4: forward cases, iff cases, failure/noAdjacentOverlap consumer
5: forward cases, iff cases, failure/noAdjacentOverlap consumer
```

This closes the intended API completion checkpoint without increasing
mathematical strength.

## Guardrails

This checkpoint only completed the bounded fixed-length API.

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

Recovered budgets remain pair-local.  The new theorems only expose which
explicit adjacent pair carries the named pair-local diagnostic inside a fixed
small list.

## File Size Watch

Current line counts after this checkpoint:

```text
  1027 lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
  1356 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
  1391 lean/dk_math/DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
  1896 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
  5670 total
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

The pressure diagnostic decomposition layer now has a coherent bounded
consumer API for the small explicit list sizes currently used by downstream
experiments.

The next safe direction is not to generalize automatically to arbitrary lists.
Instead, the next checkpoint should first identify an actual downstream caller
that needs either:

- another fixed length;
- a one-step head-or-tail view;
- or a carefully designed arbitrary-list policy.

That keeps the API evidence-driven and avoids accidental claims about
coverage, canonical choice, or global interval accounting.
