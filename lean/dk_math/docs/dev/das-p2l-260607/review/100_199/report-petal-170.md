# Report Petal 170

## Checkpoint

Checkpoint 170 introduces a bounded adjacent-diagnosis carrier for explicit
local-island witness lists.

The goal is to keep fixed-length diagnosis theorems readable before attempting
length four or a fuel-indexed generalization.  The carrier is only a result
predicate.  It is not a recursive classifier.

## Implemented Lean Surface

File:

- `DkMath.Collatz.PetalBridge.PressureAccounting`

### 1. Adjacent diagnosis carrier

```lean
def SourcePressureLocalIslandWitnessAdjacentDiagnosis
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r))
    (A B : SourcePressureLocalIslandWitness n k r) : Prop :=
  (∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
    (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
      A B hrev).items).map
      (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2)
  ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
```

Meaning:

- the recovered branch is pair-local for `A, B`,
- the overlap branch is an adjacent obstruction on the enclosing list `L`,
- no sorting, merging, coverage, or union accounting is implied.

### 2. Constructors

```lean
theorem SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {A B : SourcePressureLocalIslandWitness n k r}
    (hrev : SourcePressureLocalIslandWitnessBefore B A)
    (hbudget :
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        A B hrev).items).map
        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) :
    SourcePressureLocalIslandWitnessAdjacentDiagnosis L A B
```

```lean
theorem SourcePressureLocalIslandWitnessAdjacentDiagnosis.overlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {A B : SourcePressureLocalIslandWitness n k r}
    (hobs : SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
    SourcePressureLocalIslandWitnessAdjacentDiagnosis L A B
```

These are thin `Or` constructors.

### 3. Elimination theorem

```lean
theorem SourcePressureLocalIslandWitnessAdjacentDiagnosis.elim
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {A B : SourcePressureLocalIslandWitness n k r}
    {P : Prop}
    (hdiag : SourcePressureLocalIslandWitnessAdjacentDiagnosis L A B)
    (hrecovered :
      (∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
        (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
          A B hrev).items).map
          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) → P)
    (hoverlap : SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L → P) :
    P
```

This is useful when callers should not unfold the carrier directly.

### 4. Ordinary-failure weakening

```lean
theorem SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered_or_listFailure
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {A B : SourcePressureLocalIslandWitness n k r}
    (hdiag : SourcePressureLocalIslandWitnessAdjacentDiagnosis L A B) :
    (∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        A B hrev).items).map
        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2)
    ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L
```

This weakens only the overlap branch.  The recovered branch remains pair-local.

### 5. Length-three carrier theorem

```lean
theorem sourcePressureLocalIslandWitnessList_failure_threeDiagnosis_carrier
    {n : OddNat} {k r : ℕ}
    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
    (h1pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
    (h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
    (h3pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2, W3]) :
    SourcePressureLocalIslandWitnessAdjacentDiagnosis [W1, W2, W3] W1 W2 ∨
      SourcePressureLocalIslandWitnessAdjacentDiagnosis [W1, W2, W3] W2 W3
```

This repackages checkpoint 169's nested theorem into a compact carrier shape.

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
- length-four diagnosis,
- Collatz convergence.

Recovered budgets remain pair-local.  Overlap remains unmerged and unhandled.

The carrier is a return type for bounded diagnosis theorems, not a recursive
classifier.

## Next Inference

The carrier is stable enough to try a bounded length-four theorem next:

```text
failure [W1,W2,W3,W4]
  -> diagnosis [W1,W2]
  or diagnosis [W2,W3]
  or diagnosis [W3,W4]
```

If the length-four theorem stays readable with the carrier, it will be good
evidence for a later fuel-indexed generalization.  If it still becomes verbose,
the next step should be a more structured finite diagnosis result before any
general recursion.

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
