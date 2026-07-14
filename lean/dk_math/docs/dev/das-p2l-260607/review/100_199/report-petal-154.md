# report-petal-154

Checkpoint: 154

Subject: main root only; explicit interval-pulse-address family carrier and
bridge to pressure accounting.

## Summary

This checkpoint extended:

```text
DkMath.Collatz.PetalBridge.PressureAccounting
```

No new Lean file was created.

No `OneCycle`, `ValuationFlowBridge`, ABC, or NumberTheory files were modified.

The new API wraps explicitly supplied `SourcePressureIntervalPulseAddress`
lists as a thin family carrier and connects that carrier to the sorted/failure
and budget API from checkpoint 153.

## Family Carrier

Added:

```lean
structure SourcePressureIntervalPulseAddressFamily
    (n : OddNat) (k r : Nat) where
  items : List (SourcePressureIntervalPulseAddress n k r)
```

This carrier intentionally has no fields for:

```text
coverage
maximality
uniqueness
prefix behavior
disjointness
union accounting
convergence
```

It is just an explicit list wrapper.

## Constructors

Added:

```lean
def sourcePressureIntervalPulseAddressFamily_nil
def sourcePressureIntervalPulseAddressFamily_singleton
def sourcePressureIntervalPulseAddressFamily_cons
```

Also added:

```lean
def sourcePressureIntervalPulseAddressFamily_singleton_of_address
```

This is an alias for callers that want producer-facing wording.

Length wrappers were added:

```lean
theorem sourcePressureIntervalPulseAddressFamily_nil_length
theorem sourcePressureIntervalPulseAddressFamily_singleton_length
theorem sourcePressureIntervalPulseAddressFamily_cons_length
```

## Sorted / Failure Predicates

Added:

```lean
def SourcePressureIntervalPulseAddressFamilySortedBefore
def SourcePressureIntervalPulseAddressFamilyHasSortedBeforeFailure
```

and:

```lean
theorem sourcePressureIntervalPulseAddressFamily_sorted_or_failure
```

The failure predicate is explicitly documented in the source:

```text
Family sorted-before failure is an order obstruction only.
It does not imply interval overlap; reversed order is also a failure.
```

## Accounted-Family Lift

Added:

```lean
def sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily
```

and wrappers:

```lean
theorem sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily_length
theorem sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily_sum_le_neg_length
theorem sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily_sum_neg_of_nonempty
```

The sorted hypothesis is used only to package the converted interval-pulse
addresses as an accounted family.  The budget remains an explicit-list cost
sum, not union accounting.

## Producer Search Result

`PressureFrontier.lean` was searched for list-producing frontier objects.

Found:

```lean
def sourcePressureIntervalPulseAddress_of_localIsland
```

This produces one `SourcePressureIntervalPulseAddress` from one
`SourcePressureLocalIsland`.

No canonical producer of address lists was found in this checkpoint.

Therefore no list producer was fabricated.

Only the thin singleton producer bridge was added:

```lean
def sourcePressureIntervalPulseAddressFamily_singleton_of_localIsland
```

This packages the existing single-address producer into a singleton family.
It does not enumerate all local islands and does not cover an orbit window.

## Non-Claims

This checkpoint does not introduce:

```text
maximality
uniqueness
coverage
prefix behavior
union accounting
Collatz convergence
```

All statements remain about explicitly supplied or explicitly singleton-produced
interval-pulse addresses.

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

That warning is outside checkpoint 154.

## Next Inference

The next step should remain producer-facing but conservative:

```text
frontier object
  -> explicit address or address list, if already available
  -> SourcePressureIntervalPulseAddressFamily
  -> sorted/failure split
  -> accounted-family budget only on the sorted branch
```

Do not invent coverage.  A coverage or maximality theorem should only appear
after a real frontier producer carries those hypotheses.
