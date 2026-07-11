# report-petal-157

Checkpoint: 157

Subject: two local-island witness accounting wrappers.

## Summary

This checkpoint extended:

```text
DkMath.Collatz.PetalBridge.PressureAccounting
```

No `PressureFrontier`, `OneCycle`, `ValuationFlowBridge`, ABC, or
NumberTheory files were modified.

The new API specializes the explicit local-island witness list layer to
two supplied witnesses.

## Witness-Before Predicate

Added:

```lean
def SourcePressureLocalIslandWitnessBefore
```

This is the witness-level ordered relation obtained by converting both
witnesses to interval-pulse addresses and using:

```lean
SourcePressureIntervalPulseAddressBefore
```

Also added:

```lean
theorem sourcePressureLocalIslandWitnessBefore_iff_addressBefore
```

## Pair Sorted / Failure Iff

Added:

```lean
theorem sourcePressureLocalIslandWitnessListSortedBefore_pair_iff
theorem sourcePressureLocalIslandWitnessListHasSortedBeforeFailure_pair_iff
```

The failure theorem is explicitly documented as order failure only.

It is not overlap evidence unless additional hypotheses are supplied.

## Sorted Pair Accounted Family

Added:

```lean
def sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair
```

This packages `[W1, W2]` as an accounted family under an explicit
`SourcePressureLocalIslandWitnessBefore W1 W2` hypothesis.

## Length And Items

Added:

```lean
theorem sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair_length
theorem sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair_items
```

The item theorem records that the family contains exactly the two directly
converted accounted intervals.

## Pair Budget

Added:

```lean
theorem sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair_sum_le_neg_two
theorem sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair_sum_neg
```

These prove the sorted two-witness listed-cost bounds:

```text
sum <= -2
sum < 0
```

## Raw Local-Island Pair Wrappers

The raw argument versions were added:

```lean
theorem sourcePressureLocalIsland_pair_sum_le_neg_two
theorem sourcePressureLocalIsland_pair_sum_neg
```

They package `(j1, h1)` and `(j2, h2)` internally as explicit witnesses.

## Non-Claims

This checkpoint still does not enumerate all local islands.

It does not introduce:

```text
maximality
uniqueness
coverage
prefix behavior
union accounting
Collatz convergence
```

The pair failure theorem is not an overlap theorem.

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

That warning is outside checkpoint 157.

## Next Inference

The next conservative layer is a failure-facing pair API:

```text
not SourcePressureLocalIslandWitnessBefore W1 W2
  -> pair sorted-before failure
```

This should continue to say only "order obstruction", not overlap.  Any overlap
claim needs an extra hypothesis excluding reversed order.
