# Report: petal-290

## Goal

Strengthen separator injection to a genuine half-window packing-density theorem,
connect the bound to nonpositive pressure positions, and extract a canonical
family directly from the witness list.

## Progressive Module Split

Created:

- `DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking`

The new density and family theorems live in this module and are re-exported by
`DkMath.Collatz.PetalBridge`.  Existing carrier declarations remain temporarily
in `PressureState.lean` to avoid a cyclic aggregator/core rewrite during the
mathematical checkpoint.  Their later move is recorded as a mechanical API-
preserving refactor.

## Two-Spacing

Added:

- `SourcePressureFiniteWindowPackingUnit.eq_of_pairKey_eq`
- `.pairKey_ne_of_ne`
- `.canonicalSeparator_two_separated_of_ne_of_sorted`

Lean proves that distinct canonical packing units in a sorted witness list
satisfy:

```text
separator₁ + 2 <= separator₂
  OR separator₂ + 2 <= separator₁
```

Thus separator multiplicity one strengthens to geometric two-spacing.

## Generic Packing Lemma

Added:

- `finset_card_le_half_window_add_one_of_twoSeparated`

For a two-separated `Finset Nat` inside `[lo, hi]`:

```lean
T.card <= (hi - lo) / 2 + 1
```

The proof injects `m` into `(m - lo) / 2` and bounds the image by a finite
range.  This theorem is independent of pressure terminology.

## Sharp Pressure Packing Bound

Added:

- `sourcePressureFiniteWindowPackingUnit_card_le_half_window_add_one`

For every finite family `S` of canonical packing units:

```lean
S.card <= (hi - lo) / 2 + 1
```

This improves the previous coordinate bound from full-window capacity to
half-window packing capacity.

## Sign-Restricted Bound

Added:

- `sourcePressureNonposPositionsInWindow`
- `mem_sourcePressureNonposPositionsInWindow`
- `sourcePressureFiniteWindowPackingUnit_image_separator_subset_nonposPositions`
- `sourcePressureFiniteWindowPackingUnit_card_le_nonposPositions`

Every canonical separator belongs to the finite set of nonpositive margin
positions, hence:

```lean
S.card <= card {m in [lo, hi] | SourcePressureMarginInt n k m <= 0}
```

Added the combined local-Big surface:

- `sourcePressureFiniteWindowPackingUnit_localBig`

It exposes both half-window geometric capacity and nonpositive-position
capacity in one theorem.

## Canonical Family From The Witness List

Added:

- `sourcePressureCanonicalPackingPairFamily`
- `mem_sourcePressureCanonicalPackingPairFamily`
- `sourcePressureCanonicalPairSeparator`
- `sourcePressureCanonicalPackingPairFamily_card_le_half_window_add_one`

The family is obtained from `L.zip L.tail`, filtered by the canonical packing
state.  Therefore it represents all adjacent pair keys in `L` currently
certified as canonical finite-window packing units.

Lean proves the direct list-facing bound:

```lean
(sourcePressureCanonicalPackingPairFamily L lo hi).card
  <= (hi - lo) / 2 + 1
```

## Positive-Center Coverage Status

The canonical pair family is now extracted and bounded, but existing upstream
states only produce selected forward pairs.  They do not prove that every
positive in-window witness is a left endpoint of a canonical unit.

The exact missing contract is now named:

- `SourcePressureCanonicalLeftCoverageInWindow`

Its proposition is:

```text
for every W in L,
  if its center is positive and lies in [lo, hi],
  then there exists W' such that (W,W') has canonical packing state.
```

This did not close from `BeamSeed`, `SortedFailure`, or `FailureResolution`.
It is the precise obstruction to converting canonical-pair density into a
cardinality bound for all positive centers without an endpoint correction.

## Established Route

```text
sorted adjacent pairs
  -> multiplicity one
  -> canonical separator injection
  -> canonical separator two-spacing
  -> half-window packing density
  -> sign-restricted packing bound
  -> canonical family extracted from L
  -> exact positive-center coverage contract isolated
  -> finite local Big
```

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```

No `sorry` was introduced.

## Next Branch Prediction

Analyze list endpoints and the state-ladder selection mechanism to weaken
`SourcePressureCanonicalLeftCoverageInWindow` to a provable decomposition:

```text
positive in-window centers
  subset canonical left centers union finite boundary residue
```

The expected sharp correction is one uncovered terminal center, but that must
be derived from the actual list/state constructors rather than assumed.
