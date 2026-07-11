# report-petal-188

Date: 2026-07-06

## Scope

Checkpoint 188 is refactor-only.

The bounded diagnostic decomposition helpers were split out of
`DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis` into the new module:

```lean
DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
```

No theorem statement was intentionally strengthened, weakened, or renamed.
No length-five theorem and no arbitrary-list decomposition was added.

## New module

Created:

```text
lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
```

The new module imports:

```lean
import DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
```

It now owns the bounded length-two, length-three, and length-four helper
surface.  The original `PressureAdjacentDiagnosis` module remains the core
carrier/API module.

## Public import update

Updated:

```text
lean/dk_math/DkMath/Collatz/PetalBridge.lean
```

Added the public umbrella import:

```lean
import DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
```

No downstream pressure module needed an additional explicit import in this
checkpoint.

## Declarations moved

Address-level bounded decomposition:

```lean
theorem SourcePressureLocalIslandWitnessAdjacentPairInList.two_iff_head
theorem SourcePressureLocalIslandWitnessAdjacentPairInList.two_eq
theorem SourcePressureLocalIslandWitnessAdjacentPairInList.three_head_or_tail
theorem SourcePressureLocalIslandWitnessAdjacentPairInList.four_head_or_tail
```

Diagnostic length-two normal form:

```lean
theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_two_reversed
theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_reversed_of_two
theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.two_iff
theorem sourcePressureLocalIslandWitnessList_failure_two_exists_reversed_of_noAdjacentOverlap
```

Diagnostic length-three bounded decomposition:

```lean
theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_head_or_tail
theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_iff_head_or_tail
theorem sourcePressureLocalIslandWitnessList_failure_three_diagnostic_head_or_tail_of_noAdjacentOverlap
```

Diagnostic length-four bounded decomposition:

```lean
theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_head_or_tail
theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_iff_head_or_tail
theorem sourcePressureLocalIslandWitnessList_failure_four_diagnostic_head_or_tail_of_noAdjacentOverlap
```

These declarations now appear in
`PressureDiagnosticDecomposition.lean`, and not in `PressureAdjacentDiagnosis.lean`.

## What stayed in PressureAdjacentDiagnosis

`PressureAdjacentDiagnosis.lean` still contains the core adjacent-pair and
diagnostic infrastructure:

- adjacent-pair-in-list constructors and general API;
- list-level adjacent diagnosis carrier;
- no-adjacent-overlap predicate;
- recovered adjacent accounted-family carrier;
- diagnostic carrier definition;
- diagnostic constructors, conversions, and projections;
- nil/singleton false helpers;
- tail lift helpers;
- failure plus no-adjacent-overlap diagnostic carrier theorem;
- raw no-overlap compatibility wrappers.

## File sizes

After the split:

```text
  1356 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
   418 lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
  1391 lean/dk_math/DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
  1896 lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
  5061 total
```

The original file is now comfortably below the 1900-2000 line watch zone.

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

This was a module-boundary cleanup only.

## Verification

Commands run:

```text
lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
lake build DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
lake build DkMath.Collatz.PetalBridge.PressureAccounting
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b" DkMath/Collatz/PetalBridge/PressureAccounting.lean DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
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

## Next inference

The bounded decomposition layer now has a dedicated module.  The next checkpoint
can safely continue in one of two directions:

- add a length-five bounded decomposition in
  `PressureDiagnosticDecomposition.lean`; or
- add a downstream consumer theorem that imports the new module and uses the
  length-four decomposition.

The second option is preferable if the next proof needs evidence that the split
module is the right API boundary.
