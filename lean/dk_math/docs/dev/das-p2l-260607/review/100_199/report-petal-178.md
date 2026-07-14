# Report Petal 178

## Scope

Checkpoint 178 added consumer-facing corollaries on top of the checkpoint 177
explicit-list adjacent diagnosis theorem.

Primary file:

```text
DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
```

No supporting file changes were needed.

## Implemented Corollaries

### Failure implies recovered-or-overlap

Added:

```lean
theorem sourcePressureLocalIslandWitnessList_failure_exists_recovered_or_overlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L) :
    (∃ A B,
      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
        ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
          (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
            A B hrev).items).map
            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2)
    ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
```

This combines:

```lean
sourcePressureLocalIslandWitnessList_failure_hasAdjacentDiagnosis
SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovered_or_overlap
```

### No-overlap failure gives a recovered pair

Added:

```lean
theorem sourcePressureLocalIslandWitnessList_failure_exists_recovered_of_no_overlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L)
    (hno :
      ¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
    ∃ A B,
      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
        ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
          (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
            A B hrev).items).map
            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2
```

This eliminates the overlap branch from the recovered-or-overlap corollary.

## Proof Strategy

The first theorem is a direct projection from the list-level adjacent diagnosis
provided by checkpoint 177.

The second theorem case-splits the first theorem:

```text
recovered branch:
  return the recovered adjacent pair

overlap branch:
  contradict the supplied no-overlap hypothesis
```

## Meaning

The new API is consumer-facing:

```text
explicit-list sorted-before failure
  -> recovered adjacent pair
     or adjacent overlap obstruction
```

and under an overlap-free hypothesis:

```text
explicit-list sorted-before failure
  -> recovered adjacent pair
```

## Non-Claims

This checkpoint does not introduce:

```text
global local-island coverage
maximality
uniqueness
prefix behavior
arbitrary list sorting
canonical first diagnosis
enumeration of all diagnoses
union accounting
overlap repair
Collatz convergence
```

Recovered budgets remain pair-local.
Overlap remains an adjacent obstruction on the enclosing explicit list.

## Verification

Passed:

```bash
lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
lake build DkMath.Collatz.PetalBridge.PressureAccounting
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
git diff --check
```

No-sorry check:

```bash
rg -n "\bsorry\b" \
  DkMath/Collatz/PetalBridge/PressureAccounting.lean \
  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
```

Result: no hits.

Known unrelated build warning still appears:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

## Next Candidate

The next natural step is to introduce a small named overlap-free predicate for
explicit witness lists, then restate the no-overlap recovered theorem against
that predicate.  This would keep the consumer surface readable while avoiding
any claim that an overlap-free list exists canonically or globally.
