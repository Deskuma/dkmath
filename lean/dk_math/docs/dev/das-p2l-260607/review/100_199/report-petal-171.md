# Report Petal 171

## Checkpoint

Checkpoint 171 proves a bounded length-four failure diagnosis theorem using the
adjacent diagnosis carrier introduced in checkpoint 170.

The result remains fixed-length.  It is not a recursive classifier.

## Implemented Lean Surface

File:

- `DkMath.Collatz.PetalBridge.PressureAccounting`

### 1. Carrier tail lift

```lean
theorem SourcePressureLocalIslandWitnessAdjacentDiagnosis.lift_tail
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    {A B : SourcePressureLocalIslandWitness n k r}
    (hdiag :
      SourcePressureLocalIslandWitnessAdjacentDiagnosis (W2 :: rest) A B) :
    SourcePressureLocalIslandWitnessAdjacentDiagnosis (W1 :: W2 :: rest) A B
```

This lifts a tail diagnosis under a newly supplied head.

- recovered evidence is unchanged and remains pair-local for `A, B`;
- overlap evidence is transported to the larger enclosing list by
  `SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.of_tail`.

### 2. Length-four carrier theorem

```lean
theorem sourcePressureLocalIslandWitnessList_failure_fourDiagnosis_carrier
    {n : OddNat} {k r : ℕ}
    {W1 W2 W3 W4 : SourcePressureLocalIslandWitness n k r}
    (h1pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
    (h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
    (h3pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
    (h4pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W4).len)
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        [W1, W2, W3, W4]) :
    SourcePressureLocalIslandWitnessAdjacentDiagnosis [W1, W2, W3, W4] W1 W2 ∨
      SourcePressureLocalIslandWitnessAdjacentDiagnosis [W1, W2, W3, W4] W2 W3 ∨
        SourcePressureLocalIslandWitnessAdjacentDiagnosis [W1, W2, W3, W4] W3 W4
```

The proof uses:

- `sourcePressureLocalIslandWitnessList_failure_oneStepDiagnosis` for the head
  split;
- `sourcePressureLocalIslandWitnessList_failure_threeDiagnosis_carrier` for the
  tail `[W2, W3, W4]`;
- `SourcePressureLocalIslandWitnessAdjacentDiagnosis.lift_tail` to move tail
  diagnoses into the enclosing four-witness list.

## Optional Wrapper Decision

The optional ordinary-failure wrapper was not added.  It would expand the
return type again and work against this checkpoint's purpose: keeping bounded
diagnosis results compact through the carrier.

Callers can still use:

```lean
SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered_or_listFailure
```

on whichever branch they consume.

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
- a general recursive classifier,
- Collatz convergence.

Recovered budgets remain pair-local:

- `W1, W2`,
- `W2, W3`,
- `W3, W4`.

Overlap remains unmerged and unhandled, only propagated as adjacent obstruction
evidence on the enclosing list.

## Next Inference

The length-four theorem confirms that the adjacent diagnosis carrier keeps the
bounded result shape readable.

The next natural step is not length five by brute force.  A better next design
target is a small list-level bounded carrier such as:

```text
there exists an adjacent pair inside L with an adjacent diagnosis on L
```

The hard part is the `AdjacentPairInList` predicate.  It should be designed
carefully before introducing any fuel-indexed general classifier.

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
