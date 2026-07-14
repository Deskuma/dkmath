# Report: Petal checkpoint 181

## Summary

Checkpoint 181 exposed the actual pair-local accounted interval family object
from the recovered adjacent-family carrier.

No new carrier was necessary.  The existing
`SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily`
already stores the recovered adjacent pair and the budget over
`sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair`.
The new work is a projection with a consumer-facing `let F := ...` form.

## Existing Family Type

The accounted family object is:

```lean
structure SourcePressureAccountedIntervalFamily
    (n : OddNat) (k r : ℕ) where
  items : List (SourcePressureAccountedInterval n k r)
  pairwiseDisjoint :
    SourcePressureAccountedIntervalListPairwiseDisjoint items
```

The recovered pair-local family constructor is:

```lean
sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
  A B hrev
```

It returns `SourcePressureAccountedIntervalFamily n k r`.

## Implemented Lean Surface

Implemented in:

```text
DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
```

New projection:

```lean
theorem
  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.exists_accountedFamily
```

New consumer theorems:

```lean
theorem
  sourcePressureLocalIslandWitnessList_failure_exists_accountedFamily_of_noAdjacentOverlap

theorem
  sourcePressureLocalIslandWitnessList_failure_exists_accountedFamily_of_no_overlap
```

The projection exposes:

```lean
let F :=
  sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
    A B hrev
((F.items).map
  (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2
```

This makes the family object visible to downstream users while keeping the
proof route identical to the pair-local recovered branch.

## Guardrail Notes

The exposed family remains pair-local.  It comes from one adjacent recovered
pair `A, B` in the explicitly supplied witness list.

This checkpoint does not introduce:

- aggregation of recovered families;
- a list of all recovered families;
- a sum over all recovered families;
- disjointness between multiple recovered families;
- list-wide union accounting;
- global local-island coverage;
- maximality;
- uniqueness;
- arbitrary list sorting;
- canonical first diagnosis;
- enumeration of all diagnoses;
- overlap repair;
- Collatz convergence.

## Refactor Check

No split was needed in this checkpoint.

Current relevant file sizes after the change:

```text
940  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
1391 DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
1896 DkMath/Collatz/PetalBridge/PressureAccounting.lean
```

All are below the 2,000-line split threshold.

## Verification

Commands run from `lean/dk_math`:

```text
lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
lake build DkMath.Collatz.PetalBridge.PressureAccounting
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
```

All builds completed successfully.

No-sorry check:

```text
rg -n "\bsorry\b" \
  DkMath/Collatz/PetalBridge/PressureAccounting.lean \
  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
```

Result: no output, exit code 1, so no `sorry` was found in the checked pressure
files.

Whitespace check from repository root:

```text
git diff --check
```

Result: pass.

Known unrelated build warning remains:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

This checkpoint did not modify that file.

## Next Candidate

The next thin bridge can project facts about the exposed family itself, for
example its recovered reversed-pair length or its negative budget, while still
keeping the statement tied to one adjacent recovered pair.

That should remain a local projection from the existing family object, not an
aggregation theorem.
