# Report Petal 168

## Checkpoint

Checkpoint 168 adds weak tail-cons propagation for the one-step sorted-before
failure diagnosis built in checkpoint 167.

The scope remains local to explicit witness lists.  A diagnosis of the tail
list `W2 :: W3 :: rest` can be viewed under a newly supplied head `W1`, but a
recovered branch remains a budget for the tail head pair `W2, W3`.

## Implemented Lean Surface

File:

- `DkMath.Collatz.PetalBridge.PressureAccounting`

### 1. Tail one-step diagnosis alias

```lean
theorem sourcePressureLocalIslandWitnessList_tail_failure_oneStepDiagnosis
    {n : OddNat} {k r : ℕ}
    {W2 W3 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
    (h3pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
    (htail :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        (W2 :: W3 :: rest)) :
    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W3 W2,
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W2 W3 hrev).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
      ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
          (W2 :: W3 :: rest))
    ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        (W3 :: rest)
```

This is a naming alias for applying the existing one-step diagnosis to a tail
list.  The unused `W1` from the suggested shape was intentionally omitted,
because the theorem itself does not depend on a new head.

### 2. Tail overlap lift

```lean
theorem sourcePressureLocalIslandWitnessList_tailDiagnosis_overlap_lift
    {n : OddNat} {k r : ℕ}
    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (hobs :
      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
        (W2 :: W3 :: rest)) :
    SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
      (W1 :: W2 :: W3 :: rest)
```

This propagates a tail adjacent-overlap obstruction under a new head.  It does
not merge or repair the overlap.

### 3. Weak tail diagnosis under cons

```lean
theorem sourcePressureLocalIslandWitnessList_tailFailure_oneStepDiagnosis_under_cons
    {n : OddNat} {k r : ℕ}
    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
    (h3pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
    (htail :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        (W2 :: W3 :: rest)) :
    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W3 W2,
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W2 W3 hrev).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
      ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
          (W1 :: W2 :: W3 :: rest))
    ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        (W3 :: rest)
```

This is the main cp168 theorem.  It lifts only the obstruction branch through
the new head.  The recovered branch remains the tail-pair recovered budget.

### 4. Optional ordinary failure wrapper

```lean
theorem
    sourcePressureLocalIslandWitnessList_tailFailure_oneStepDiagnosis_under_cons_or_listFailure
    {n : OddNat} {k r : ℕ}
    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
    (h3pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
    (htail :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        (W2 :: W3 :: rest)) :
    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W3 W2,
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W2 W3 hrev).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
      ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
          (W1 :: W2 :: W3 :: rest))
    ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        (W3 :: rest)
```

This wrapper weakens the lifted overlap obstruction to ordinary full-list
sorted-before failure for callers that do not need obstruction-specific
evidence.

## Boundary Notes

This checkpoint intentionally does not introduce:

- maximality,
- uniqueness of pressure families,
- coverage,
- prefix behavior,
- union accounting,
- interval merging,
- arbitrary list sorting,
- arbitrary list failure classification,
- Collatz convergence.

Recovered budget remains a tail-pair budget.  It is not promoted into a
full-list budget.

Overlap remains unmerged and unhandled.  The code only propagates the local
adjacent obstruction.

## Next Inference

The next safe direction is a bounded recursive diagnosis skeleton for a fixed
short list, starting with length three:

```text
failure [W1, W2, W3]
  -> head recovered
  or head overlap obstruction
  or tail recovered
  or tail overlap obstruction
```

This should still avoid a general sorting algorithm.  Once length-three and
length-four surfaces stabilize, a fuel-indexed diagnosis structure can be
designed from the observed pattern.

## Verification

- PASS: `lake build DkMath.Collatz.PetalBridge.PressureAccounting`
- PASS: `lake build DkMath.Collatz.PetalBridge.PressureFrontier`
- PASS: `lake build DkMath.Collatz.PetalBridge`
- PASS: `rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean`
  produced no hits.
- PASS: `rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean`
  produced no hits.
- PASS: `git diff --check`

Build note: the existing unrelated warning from
`DkMath.NumberTheory.ZsigmondyCyclotomicResearch` still reports a declaration
using `sorry`.  This checkpoint did not edit that file, and the two target
Collatz/PetalBridge files checked above have no `sorry` hits.
