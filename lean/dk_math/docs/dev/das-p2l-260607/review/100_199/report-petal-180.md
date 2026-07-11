# Report: Petal checkpoint 180

## Summary

Checkpoint 180 packaged the no-adjacent-overlap recovered branch as a named
pair-local accounted-family carrier.

The new carrier says only that the explicit witness list contains one adjacent
pair `A, B` whose reversed order gives the existing pair-local accounted
interval family with budget `≤ -2`.

It does not aggregate multiple recovered pairs and does not introduce
list-level union accounting.

## Implemented Lean Surface

Implemented in:

```text
DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
```

New carrier:

```lean
def SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
  ∃ A B,
    SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
      ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
        (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
          A B hrev).items).map
          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2
```

New API:

```lean
theorem
  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.of_pair

theorem
  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.exists_pair

theorem
  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.nil_false

theorem
  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.singleton_false

theorem
  sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamily_of_noAdjacentOverlap

theorem
  sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamily_of_no_overlap
```

The raw-negation wrapper was added for callers that still store the no-overlap
branch as:

```lean
¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
```

The named no-overlap theorem uses:

```lean
SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction L
```

## Guardrail Notes

This checkpoint only packages one recovered adjacent pair and its existing
pair-local accounted interval family.

It does not assert:

- list-level union accounting;
- aggregation of multiple recovered pairs;
- global local-island coverage;
- maximality;
- uniqueness;
- prefix behavior;
- arbitrary list sorting;
- canonical first diagnosis;
- enumeration of all diagnoses;
- overlap repair;
- existence of a canonical overlap-free list;
- Collatz convergence.

Recovered budgets remain pair-local.  Overlap remains an adjacent obstruction
on the enclosing explicit list.

## Style Note

The two consumer-facing theorem names are long because they intentionally
encode the whole proof route:

```text
failure + noAdjacentOverlap -> hasRecoveredAdjacentAccountedFamily
failure + raw no_overlap    -> hasRecoveredAdjacentAccountedFamily
```

The declarations use local `set_option linter.style.longLine false in`
wrappers so the searchable theorem names remain intact without affecting the
rest of the file.

## Refactor Check

No split was needed in this checkpoint.

Current relevant file sizes after the change:

```text
860  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
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

The next thin bridge can project from
`SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily L` to
an explicit existential over the accounted interval family object itself, so a
consumer can use the family without unpacking the adjacent pair manually.

That bridge should still remain pair-local and avoid any claim about list-wide
union accounting or aggregation.
