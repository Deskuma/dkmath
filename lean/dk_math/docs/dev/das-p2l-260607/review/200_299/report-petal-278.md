# Report: petal-278

## Goal

Split the boundary corridor into contact-or-gap cases.

## Implemented

Added:

- `SourcePressureForwardPairComparisonState.boundary_corridor_eq_or_lt`
- `SourcePressureForwardPairComparisonState.right_val_eq_left_add_two_or_left_add_two_lt_right_val`

The index-level split uses:

- `SourcePressureForwardPairComparisonState.left_next_boundary_le_right_previous_boundary`

The value-level split uses:

- `SourcePressureForwardPairComparisonState.left_succ_lt_right_val`

## Established Fact

For any concrete forward pair comparison state

```lean
h : SourcePressureForwardPairComparisonState L W W'
```

Lean now proves the boundary corridor dichotomy:

```lean
r + W.val + 1 = r + (W'.val - 1)
  ∨ r + W.val + 1 < r + (W'.val - 1)
```

and the value-level version:

```lean
W'.val = W.val + 2 ∨ W.val + 2 < W'.val
```

## What Can Be Concluded

The corridor between a forward pair's two positive centers has only two local
arithmetic shapes:

- contact corridor: the left next boundary and right previous boundary are the
  same index;
- genuine gap corridor: the left next boundary is strictly before the right
  previous boundary.

At the witness-value level, this says the right center is either exactly two
steps after the left center, or strictly farther away.  This is stronger and
more usable than merely knowing `W.val + 1 < W'.val`.

## Guardrails

This is still a local arithmetic split for an explicit forward pair comparison
state.  It does not prove that every index inside a genuine corridor is
nonpositive, nor does it prove global coverage, uniqueness, arbitrary window
disjointness, or Collatz termination.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
```

Final whitespace gate:

```text
git diff --check
```

## Implementation Note

The value-level theorem name is intentionally long because it is used as a
searchable public surface.  The surrounding code locally disables the long-line
linter for that single declaration and immediately re-enables it afterwards.

## Next Branch Prediction

The next useful split is likely to combine `boundary_corridor_surface` with
`boundary_corridor_eq_or_lt`, producing a sign-bundled contact-or-gap theorem.
That would let callers branch directly into:

- contact with one shared nonpositive boundary;
- strict corridor with two ordered nonpositive endpoints.
