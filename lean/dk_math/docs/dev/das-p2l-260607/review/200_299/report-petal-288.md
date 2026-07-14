# Report: petal-288

## Goal

Move from one finite-window packing unit to the first reusable comparison
carrier for two units, and expose separator reuse as an explicit branch.

## Implemented

Added:

- `SourcePressureFiniteWindowPackingPairComparisonState`

The state stores two `SourcePressureFiniteWindowPackingSeparatorState` values
in the same witness list and finite window.

Added basic projections:

- `.left`
- `.right`
- `.left_order_chain`
- `.right_order_chain`
- `.left_window_width`
- `.right_window_width`

Added the separator branch point and branch surfaces:

- `.separator_eq_or_ne`
- `.separator_eq_surface`
- `.separator_ne_surface`

## Additional Results

Added two consequences inferred from the successful comparison surface:

- `.shared_separator_cross_surface`
- `.separator_lt_or_gt`

In the reuse branch `m₁ = m₂`, Lean proves that the common separator lies
strictly inside both open center intervals:

```text
leftCenter₁ < m₁ < rightCenter₁
leftCenter₂ < m₁ < rightCenter₂
```

Thus separator reuse is now represented as an explicit intersection witness
for the two consumed intervals.

In the distinct branch `m₁ ≠ m₂`, Lean proves the strict order split:

```text
m₁ < m₂ ∨ m₂ < m₁
```

This gives the next comparison layer a canonical ordered-separator branch.

## Established Facts

For two finite-window packing units, exactly one of the following forms is
available:

1. They reuse one separator, which is a common point of both open center
   intervals.
2. They use distinct separators, which are strictly ordered in the finite
   window.

Both branches retain the complete ordered chains:

```text
lo <= leftCenterᵢ < mᵢ < rightCenterᵢ <= hi
```

This is the first pairwise invariant suitable for analyzing separator
multiplicity before passing to a finite family.

## Route

```text
finite-window ordered chain
  -> one pair consumes three ordered positions
  -> pair-of-packings comparison
  -> separator reuse / distinct split
  -> shared-point geometry or ordered separators
  -> prepares bounded multiplicity and packing count
  -> local Big
```

## Refactoring Note

`PressureState.lean` exceeds the preferred 2,000-line size.  A source-level
TODO now records the intended mechanical extraction of this stabilized API to
`PressureState/FiniteWindowPacking.lean`.  No import graph was changed in this
checkpoint.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```

No `sorry` was introduced.

## Next Branch Prediction

Refine the reuse branch by comparing pair identities or center intervals.  The
smallest useful question is whether a common separator plus an existing
adjacency/sortedness invariant bounds the number of pairs that can contain that
separator.  If no sharp bound follows, define an explicit separator
multiplicity predicate for a finite selected-pair family and carry the bound as
the counting hypothesis.
