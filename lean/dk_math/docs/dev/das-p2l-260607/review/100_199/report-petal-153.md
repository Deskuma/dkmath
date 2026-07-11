# report-petal-153

Checkpoint: 153

Subject: main root only; lift explicit interval-pulse-address lists into the
`PressureAccounting` family and obstruction API.

## Summary

This checkpoint stayed in:

```text
DkMath.Collatz.PetalBridge.PressureAccounting
```

No `OneCycle`, `ValuationFlowBridge`, or ABC files were modified.

The core move was to lift the existing single-address bridge:

```lean
sourcePressureAccountedInterval_of_intervalPulseAddress
```

from one `SourcePressureIntervalPulseAddress` to explicit lists, sorted-list
predicates, sorted families, budget wrappers, and pair-level failure facts.

All claims remain about explicitly supplied interval-pulse addresses.  Nothing
new claims maximality, uniqueness, coverage, prefix behavior, union accounting,
or Collatz convergence.

## Added List Conversion

Chosen name:

```lean
def sourcePressureAccountedIntervalList_of_intervalPulseAddressList
```

It is the direct map:

```lean
L.map sourcePressureAccountedInterval_of_intervalPulseAddress
```

Length wrapper added:

```lean
theorem sourcePressureAccountedIntervalList_of_intervalPulseAddressList_length
```

## Added Pulse-Address List Budget

Implemented:

```lean
theorem sourcePressureIntervalPulseAddressList_sum_le_neg_length
```

This proves that the converted list of explicit address witnesses contributes
at most `-L.length` to the summed interval net drop.

Also added the nonempty corollary:

```lean
theorem sourcePressureIntervalPulseAddressList_sum_neg_of_nonempty
```

This is an extra convenience theorem inferred after the main budget theorem
passed.

## Added Pulse-Address Sorted / Failure Layer

Implemented:

```lean
def SourcePressureIntervalPulseAddressListSortedBefore
def SourcePressureIntervalPulseAddressListHasSortedBeforeFailure
theorem sourcePressureIntervalPulseAddressList_sorted_or_failure
```

These are defined through the accounted-list conversion, so they inherit the
existing sorted/failure dichotomy.

Important comment preserved in code:

```text
not before != overlap
```

A sorted-before failure only says that the chosen left-to-right adjacent order
failed.  The interval may be reversed rather than overlapping.

## Added Direct Pulse-Address Before Predicate

Optional part F was implemented.

Added:

```lean
def SourcePressureIntervalPulseAddressBefore
theorem sourcePressureIntervalPulseAddressBefore_iff_accountedBefore
```

This gives the direct address-level predicate:

```lean
A.start + A.len <= B.start
```

and proves that it agrees with the accounted-interval predicate after
conversion.

## Added Pair-Level Pulse Facts

As an extra small API layer, added:

```lean
theorem sourcePressureIntervalPulseAddressListSortedBefore_pair_iff
theorem sourcePressureIntervalPulseAddressListHasSortedBeforeFailure_pair_iff
```

These make two-address examples easy to read:

```text
[A, B] sorted  <-> A before B
[A, B] failure <-> not A before B
```

Again, the failure theorem is not an overlap theorem.

## Added Sorted Family Lift

Implemented:

```lean
def sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList
```

and wrappers:

```lean
theorem sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList_length
theorem sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList_sum_le_neg_length
theorem sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList_sum_neg_of_nonempty
```

The sorted hypothesis is used to package the converted list as a pairwise
disjoint family.  The budget theorem remains the explicit-list budget.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.PressureAccounting
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
```

The `rg` check returned no matches.

The build still reports the existing unrelated warning:

```text
DkMath.NumberTheory.ZsigmondyCyclotomicResearch uses sorry
```

This is outside checkpoint 153.

## Next Inference

The next natural main-root step is to connect this pulse-address list layer to
the nearest orbit-window or frontier producer:

```text
producer of explicit SourcePressureIntervalPulseAddress list
  -> sorted/failure split
  -> if sorted: accounted family and budget
  -> if failure: obstruction evidence kept first-class
```

The key design rule should remain:

```text
failure is order failure first, overlap only with extra hypotheses.
```
