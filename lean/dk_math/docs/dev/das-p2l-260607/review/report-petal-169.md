# Report Petal 169

## Checkpoint

Checkpoint 169 adds a bounded length-three diagnosis theorem for explicit
local-island witness lists.

The theorem is deliberately not recursive.  It only says that a failure in
`[W1, W2, W3]` is diagnosed by one of its two adjacent pairs:

- head pair `W1, W2`,
- tail pair `W2, W3`.

Recovered budgets remain attached to the adjacent pair that produced them.

## Implemented Lean Surface

File:

- `DkMath.Collatz.PetalBridge.PressureAccounting`

### 1. Empty and singleton no-failure facts

```lean
theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure_nil_false
    {n : OddNat} {k r : ℕ} :
    ¬ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
      ([] : List (SourcePressureLocalIslandWitness n k r))
```

```lean
theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure_singleton_false
    {n : OddNat} {k r : ℕ}
    {W : SourcePressureLocalIslandWitness n k r} :
    ¬ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W]
```

The singleton theorem is a name-aligned alias of the older
`sourcePressureLocalIslandWitnessList_no_failure_singleton`.

### 2. Tail pair diagnosis under a new head

```lean
theorem sourcePressureLocalIslandWitnessList_tailPair_failure_under_cons_diagnosis
    {n : OddNat} {k r : ℕ}
    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
    (h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
    (h3pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
    (htail :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W2, W3]) :
    (∃ hrev : SourcePressureLocalIslandWitnessBefore W3 W2,
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W2 W3 hrev).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
    ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
        [W1, W2, W3]
```

This consumes the cp168 weak tail diagnosis under cons.  The impossible deeper
branch is `SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W3]`,
which is eliminated by the singleton no-failure theorem.

### 3. Length-three diagnosis

```lean
theorem sourcePressureLocalIslandWitnessList_failure_threeDiagnosis
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
    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W1 W2 hrev).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
      ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
          [W1, W2, W3])
    ∨
    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W3 W2,
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W2 W3 hrev).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
      ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
          [W1, W2, W3])
```

The first branch is the head pair diagnosis.  The second branch is the tail
pair diagnosis lifted under the original head.

### 4. Optional ordinary-failure wrapper

```lean
theorem sourcePressureLocalIslandWitnessList_failure_threeDiagnosis_or_listFailure
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
    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W1 W2 hrev).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
      ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
          [W1, W2, W3])
    ∨
    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W3 W2,
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W2 W3 hrev).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
      ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
          [W1, W2, W3])
```

This weakens overlap branches to ordinary sorted-before failure of the same
three-witness list.

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

The theorem is bounded to length three only.  Recovered budgets remain
pair-local:

- `W1, W2` in the head recovered branch,
- `W2, W3` in the tail recovered branch.

Overlap remains unmerged and unhandled.

## Next Inference

The length-three theorem shows that direct nested `Or` return types are already
large.  Before length four, it may be worth introducing a small bounded result
type, for example a local adjacent-pair diagnosis carrier with two constructors:

```text
recovered pair-local budget
adjacent overlap obstruction on the enclosing list
```

That would keep a length-four theorem readable without introducing a general
recursive classifier.  The alternative is to add length-four directly and use
the resulting type verbosity as evidence for the final carrier shape.

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
