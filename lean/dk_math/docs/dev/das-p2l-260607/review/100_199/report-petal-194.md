# Report Petal 194

## Checkpoint

Checkpoint 194 reviewed the bridge policy between the adjacent-diagnosis layer
and the recovered pair-cases layer.

This was a design-only checkpoint.  No Lean source theorem was added.

Primary inspected files:

- `DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean`
- `DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean`
- `DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean`
- `DkMath/Collatz/PetalBridge/PressureAccounting.lean`
- `DkMath/Collatz/PetalBridge/PressureFrontier.lean`

## Searched Declarations

Searched for:

```text
sourcePressureLocalIslandWitnessList_failure_exists_recovered_or_overlap
sourcePressureLocalIslandWitnessList_failure_exists_recovered_of_noAdjacentOverlap
sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
SourcePressureLocalIslandWitnessAdjacentDiagnosis
SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction
SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
```

## Existing Bridge Chain

The clean bridge already exists in `PressureAdjacentDiagnosis.lean`.

The layer path is:

```text
sorted-before failure
  -> recovered pair OR adjacent-overlap obstruction

sorted-before failure + no-adjacent-overlap
  -> recovered pair

sorted-before failure + no-adjacent-overlap
  -> recovered adjacent accounted-family diagnostic
```

The key declarations are:

```lean
theorem sourcePressureLocalIslandWitnessList_failure_exists_recovered_or_overlap
theorem sourcePressureLocalIslandWitnessList_failure_exists_recovered_of_noAdjacentOverlap
theorem sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
```

This is already the exact branch-cut policy needed to move from adjacent
diagnosis to recovered pair-local accounting.

## Layer Distinction

### Adjacent Diagnosis

The adjacent-diagnosis layer is represented by:

```lean
def SourcePressureLocalIslandWitnessAdjacentDiagnosis
def SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
```

This layer says that an adjacent pair in the explicit list has a local
diagnosis.  The diagnosis may be:

```text
recovered pair-local budget evidence
or adjacent-overlap obstruction
```

It does not require no-overlap.  Therefore it is intentionally weaker and more
branch-aware than recovered accounting.

### Overlap Obstruction

The overlap branch is represented by:

```lean
def SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
def SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction
```

The named no-overlap predicate is a thin wrapper around negating the adjacent
overlap obstruction.  It is not a global coverage, maximality, sortedness, or
repair statement.  It only removes the obstruction branch for the explicit
list under discussion.

### Recovered Pair-Local Accounting

The recovered-accounting layer is represented by:

```lean
def SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
def SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
```

This layer stores one recovered adjacent pair, its reversed-before witness, a
pair-local accounted interval family, budget evidence, strict negativity, and
length-two structure.

It remains pair-local.  It does not aggregate multiple recovered pairs or
produce a list-wide union.

## Bounded Pair-Cases Surface

The fixed-window consumer API is already present in
`PressureDiagnosticDecomposition.lean`.

For lengths two through five, the consumer can use:

```lean
theorem sourcePressureLocalIslandWitnessList_failure_two_pairDiagnostic_cases_of_noAdjacentOverlap
theorem sourcePressureLocalIslandWitnessList_failure_three_pairDiagnostic_cases_of_noAdjacentOverlap
theorem sourcePressureLocalIslandWitnessList_failure_four_pairDiagnostic_cases_of_noAdjacentOverlap
theorem sourcePressureLocalIslandWitnessList_failure_five_pairDiagnostic_cases_of_noAdjacentOverlap
```

These theorems are the correct current bridge endpoint when the caller has:

```text
fixed list length
+ sorted-before failure
+ no-adjacent-overlap
```

They expose the recovered branch as a finite disjunction of explicit adjacent
pair diagnostics.

## No New Wrapper Added

No additional bridge theorem was added.

Reason:

- `failure + noAdjacentOverlap -> recovered diagnostic` already exists.
- fixed length two through five pair-cases already exist.
- adding a name such as a length-five recovered-pair-cases bridge would only
  duplicate
  `sourcePressureLocalIslandWitnessList_failure_five_pairDiagnostic_cases_of_noAdjacentOverlap`.

The next theorem should be added only when a concrete downstream proof needs a
specific consumer shape that is not already covered by the existing API.

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

The distinction remains:

```text
adjacent diagnosis:
  recovered OR overlap

no-overlap:
  removes the overlap branch

recovered pair-local accounting:
  one explicit adjacent pair with one accounted family
```

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

The bridge design is now explicit enough to guide the next implementation.

The next safe move should be consumer-driven:

- if a downstream proof has no-overlap, use the bounded pair-cases API;
- if it only has adjacent diagnosis, keep the recovered-or-overlap branch;
- if it needs recovered accounting, make the no-overlap branch-cut explicit.

Do not add length six or arbitrary-list machinery until a concrete downstream
proof needs it.
