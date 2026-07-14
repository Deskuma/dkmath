# Report: petal-289

## Goal

Turn the pairwise separator comparison into a genuine multiplicity theorem,
canonicalize separators, and continue through the first finite-family packing
bound.

## Ordered Adjacent-Pair Bridge

Added:

- `sourcePressureLocalIslandWitnessBefore_val_lt`
- `sourcePressureSortedWitnessList_head_val_le_of_mem`
- `sourcePressureAdjacentPairs_eq_or_nonoverlap_of_sorted`

For two oriented adjacent pairs in one sorted witness list, Lean proves:

```text
same oriented pair
  OR right₁ <= left₂
  OR right₂ <= left₁
```

The weak endpoint inequalities are exact: consecutive pairs may share one
witness endpoint.

## Multiplicity One

Added adjacent-pair projections from both finite-window carriers, then proved:

- `SourcePressureFiniteWindowPackingPairComparisonState.same_pair_of_shared_separator_of_sorted`
- `SourcePressureFiniteWindowPackingPairComparisonState.separators_ne_of_pairs_ne_of_sorted`

The established equivalence direction is:

```text
shared separator + sorted list
  -> same oriented adjacent pair

distinct oriented adjacent pairs + sorted list
  -> distinct separators
```

Thus one separator has multiplicity at most one among oriented adjacent-pair
packing units in a sorted witness list.

## Canonical Packing

Added:

- `SourcePressureCanonicalFiniteWindowPackingState`
- `.finiteWindow`
- `.separator_nonpos`
- `.separator_between_centers`
- `.separator_in_window`
- `.adjacentPair`
- `SourcePressureForwardPairComparisonState.to_canonicalFiniteWindowPackingState`

The canonical separator is:

```lean
r + W.val + 1
```

It is nonpositive, lies strictly between the positive centers, and belongs to
the same finite window.

## Finite-Family Carrier And Injection

Added:

- `SourcePressureFiniteWindowPackingUnit`
- `SourcePressureFiniteWindowPackingUnit.canonicalSeparator`
- `SourcePressureFiniteWindowPackingUnit.pairKey`
- `.canonicalSeparator_in_window`
- `.canonicalSeparator_ne_of_pairKey_ne_of_sorted`
- `.canonicalSeparator_injective_of_sorted`

The unit structure packages an oriented pair with its canonical finite-window
state.  Under sortedness, canonical separator is injective on the full unit
type, not merely on a chosen family.

## Finite-Window Packing Bound

Added:

- `sourcePressureFiniteWindowPackingUnit_card_le_window_card`
- `sourcePressureFiniteWindowPackingUnit_card_le_window_width_add_one`

For every finite family `S` of canonical packing units:

```lean
S.card <= hi + 1 - lo
```

For a nonempty family, the conventional form is also available:

```lean
S.card <= hi - lo + 1
```

The proof maps every unit injectively to its canonical separator in
`Finset.Icc lo hi` and applies `Nat.card_Icc`.

## Established Route

```text
two packing units
  -> adjacent-pair order dichotomy
  -> shared separator forces same oriented pair
  -> distinct pairs have distinct canonical separators
  -> separator injection on finite families
  -> card units <= card [lo, hi]
  -> finite-window packing bound
  -> local Big
```

This checkpoint reaches the first actual counting theorem.  Separator reuse is
not carried as an assumed multiplicity bound: sorted adjacency proves its
multiplicity is one.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```

No `sorry` was introduced.

## Refactoring Status

The finite-window API is now large enough to extract mechanically into
`PressureState/FiniteWindowPacking.lean`.  The source TODO remains authoritative.
The move should be a dedicated checkpoint because the current theorem chain is
stable and fully built.

## Next Branch Prediction

The current bound counts packing units by all separator positions.  The next
mathematical strengthening is to count only nonpositive separator positions:

```text
card packing units
  <= card {m in [lo, hi] | margin(m) <= 0}
  <= hi + 1 - lo
```

This refined image theorem would connect packing density directly to the sign
distribution inside the finite window.
