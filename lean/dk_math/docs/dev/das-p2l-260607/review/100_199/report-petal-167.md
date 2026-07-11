# Report Petal 167

## Checkpoint

Checkpoint 167 closes the one-layer decomposition of explicit witness-list
sorted-before failure.

The goal was intentionally narrow:

- peel one recursive head/tail layer,
- diagnose a head failure by the existing pair-level recovered-or-obstruction
  split,
- return a tail failure as a tail branch,
- avoid any global sorting algorithm or union accounting.

## Implemented Lean Surface

File:

- `DkMath.Collatz.PetalBridge.PressureAccounting`

### 1. Head-or-tail decomposition

```lean
theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.head_or_tail
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        (W1 :: W2 :: rest)) :
    (¬ SourcePressureLocalIslandWitnessBefore W1 W2) ∨
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        (W2 :: rest)
```

This is the inverse direction to the cp166 constructors.  It says that an
adjacent sorted-before failure in a nontrivial explicit witness list is either
already visible at the head pair, or it lives in the tail list.

### 2. Iff form

```lean
theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_iff_head_or_tail
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)} :
    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        (W1 :: W2 :: rest) ↔
      (¬ SourcePressureLocalIslandWitnessBefore W1 W2) ∨
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
          (W2 :: rest)
```

This packages the constructor direction from cp166 and the new decomposition
direction from this checkpoint.

### 3. Head not-before diagnosis

```lean
theorem
    sourcePressureLocalIslandWitnessList_headNotBefore_recovered_or_adjacentOverlapObstruction
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (h1pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
    (h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
    (hnot : ¬ SourcePressureLocalIslandWitnessBefore W1 W2) :
    (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W1 W2 hrev).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
    ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
        (W1 :: W2 :: rest)
```

This converts a raw head not-before proof into the existing pair-level
diagnosis.  If the pair can be reversed, the recovered budget appears at the
pair level.  Otherwise the result is recorded as an adjacent overlap
obstruction on the surrounding list.

### 4. One-step diagnosis

```lean
theorem sourcePressureLocalIslandWitnessList_failure_oneStepDiagnosis
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (h1pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
    (h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        (W1 :: W2 :: rest)) :
    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W1 W2 hrev).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
      ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
          (W1 :: W2 :: rest))
    ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        (W2 :: rest)
```

This is a one-step diagnostic surface:

- head failure: pair-level recovered branch or adjacent overlap obstruction,
- tail failure: returned unchanged as a tail sorted-before failure.

It is not a recursive list classifier.

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

The overlap branch remains unmerged and unhandled.  It is only named as an
adjacent obstruction.

## Next Inference

The next safe theorem direction is tail-cons propagation for the diagnostic
surface, but only in the weak form:

```text
tail failure diagnosis can be lifted as a tail branch under a new head
```

The recovered-budget branch should not be promoted to a full-list recovered
budget without additional accounting hypotheses, because the recovered pair may
live strictly inside the tail.

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
