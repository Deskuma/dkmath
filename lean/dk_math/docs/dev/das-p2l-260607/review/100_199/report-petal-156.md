# report-petal-156

Checkpoint: 156

Subject: singleton local-island witness accounting wrappers.

## Summary

This checkpoint extended:

```text
DkMath.Collatz.PetalBridge.PressureAccounting
```

No `PressureFrontier`, `OneCycle`, `ValuationFlowBridge`, ABC, or
NumberTheory files were modified.

The new API specializes the checkpoint-155 explicit local-island witness list
layer to the singleton case.

## Singleton Sortedness

Added:

```lean
theorem sourcePressureLocalIslandWitnessListSortedBefore_singleton
```

This proves that `[W]` is sorted after conversion to a pulse-address family.

Also added:

```lean
theorem sourcePressureLocalIslandWitnessList_no_failure_singleton
```

This records that a singleton witness list cannot carry an adjacent
sorted-before failure.

## Singleton Accounted Family

Added:

```lean
def sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness
```

This is the singleton specialization of:

```lean
sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList
```

Length wrapper:

```lean
theorem sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness_length
```

## Singleton Budget

Added:

```lean
theorem sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness_sum_le_neg_one
theorem sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness_sum_neg
```

These are the singleton `<= -1` and strict-negative listed-cost facts.

## Item Consistency

Added:

```lean
theorem sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness_items
```

This proves that the singleton accounted family contains exactly the direct
accounted interval obtained from:

```lean
sourcePressureIntervalPulseAddress_of_localIslandWitness W
```

## Raw Local-Island Theorems

Added raw-argument wrappers:

```lean
theorem sourcePressureLocalIsland_singleton_sum_le_neg_one
theorem sourcePressureLocalIsland_singleton_sum_neg
```

These package `(j, hisland)` internally as one explicit
`SourcePressureLocalIslandWitness`.

## Non-Claims

This checkpoint still does not enumerate all local islands.

It also does not introduce:

```text
maximality
uniqueness
coverage
prefix behavior
union accounting
Collatz convergence
```

All statements remain about one explicitly supplied local-island witness.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.PressureAccounting
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
```

The `rg` checks returned no matches.

The build still reports the existing unrelated warning:

```text
DkMath.NumberTheory.ZsigmondyCyclotomicResearch uses sorry
```

That warning is outside checkpoint 156.

## Next Inference

The next natural step is the two-witness layer:

```text
[W1, W2]
  -> sorted iff first converted address is before the second
  -> failure iff that ordered relation fails
  -> sorted branch gives length 2 and budget <= -2
```

This should remain an explicit-list theorem.  It must not be read as an
overlap theorem unless additional hypotheses are supplied.
