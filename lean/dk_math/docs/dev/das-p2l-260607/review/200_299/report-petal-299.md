# Petal implementation report 299

## Scope

This checkpoint continued the Float/Petal branch through the first genuine API
boundary rather than stopping at the historical review number.

## Implemented

### Exact debt/payment ledger

`FloatWindow/DriftBridge.lean` now defines `sumExtraHeight` and proves

```text
final bit width + accumulated extra height
  = initial bit width + number of carry-two events.
```

Thus `s - 1` is an exact lower payment against upper binary-width debt.

### Growth-channel decomposition

Finite orbit counts were added for all width growth, `3 mod 8` growth, and
`7 mod 8` growth.  The implementation proves:

```text
all growth = three-channel growth + seven-channel growth
three-channel growth <= delayed height-at-least-two receivers
all growth <= delayed receivers + seven-channel reservoir.
```

The explicit carry-two, height-one, `7 mod 8` reservoir count is proved equal
to the seven-channel growth count.  It is not conflated with all `7 mod 8`
states.

### Exact carry threshold

`FloatWindow/Core.lean` now proves that a positive state's own-width carry is
two exactly when `3*n+1` crosses `2^(bitWidth n + 1)`.  This gives an exact
binary-boundary characterization with no analytic approximation.

### Observation audit

`DyadicFloatSignature` was introduced without the original state value.
Compatibility is now represented by equality with the canonical signature.
The API explicitly separates within-width, disjoint-window, and overlapping-
window conditions.  No uniqueness or candidate-cardinality claim is made from
`middleGapCapacity = 1` alone.

## Genuine stopping point

The Float ledger is indexed by orbit slots, while `SourcePressureMarginInt` is
indexed by source-depth coordinates `r + j`.  The workspace currently has no
theorem mapping an orbit payment slot to a pressure-depth slot while preserving
its height contribution.  Therefore a pressure payment-collision theorem is
not presently derivable without inventing an index identification.

This missing contract is recorded next to the code in `DriftBridge.lean`.  The
next legitimate implementation must define that map and prove contribution
preservation before translating Float collisions into pressure-margin facts.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.DriftBridge
lake build DkMath.Collatz.PetalBridge.FloatWindow.DyadicFloat
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath.Collatz.PetalBridge
git diff --check
```

The new FloatWindow files contain no `sorry` or `axiom` declarations.

