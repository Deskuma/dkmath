# Report: Petal checkpoint 179

## Summary

Checkpoint 179 added a named no-adjacent-overlap predicate for explicit
source-pressure local-island witness lists.

The new predicate is intentionally only a readability wrapper around the
existing adjacent-overlap obstruction negation:

```lean
def SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
  ¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
```

This keeps the cp178 theorem surface intact while giving downstream callers a
named hypothesis instead of a raw negation.

## Implemented Lean Surface

Implemented in:

```text
DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
```

New API:

```lean
def SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction

theorem
  SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction.not_obstruction

theorem
  SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction.of_not

theorem
  SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction.nil

theorem
  SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction.singleton

theorem
  sourcePressureLocalIslandWitnessList_failure_exists_recovered_of_noAdjacentOverlap
```

The consumer theorem is the named-hypothesis version of the cp178 raw-negation
theorem:

```lean
sourcePressureLocalIslandWitnessList_failure_exists_recovered_of_no_overlap
```

Its conclusion is unchanged: from a sorted-before failure and no adjacent
overlap obstruction, one adjacent pair in the supplied explicit list carries a
pair-local recovered budget.

## Guardrail Notes

This checkpoint does not introduce a broader overlap-free concept.

In particular, it does not assert:

- existence of a canonical overlap-free list;
- global local-island coverage;
- maximality;
- uniqueness;
- prefix behavior;
- arbitrary list sorting;
- canonical first diagnosis;
- enumeration of all diagnoses;
- union accounting;
- overlap repair;
- Collatz convergence.

Recovered budgets remain pair-local.  Overlap remains an adjacent obstruction
on the enclosing explicit list.

## Refactor Check

No split was needed in this checkpoint.

Current relevant file sizes after the change:

```text
742  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
1391 DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
```

Both remain below the 2,000-line split threshold.

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

The next thin bridge can use the named no-adjacent-overlap predicate to package
the recovered adjacent pair into an existing pair-local accounted interval
family.  That should still avoid union accounting: it should only re-expose the
one recovered pair already produced by
`sourcePressureLocalIslandWitnessList_failure_exists_recovered_of_noAdjacentOverlap`.
