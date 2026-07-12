# Report: petal-272

## Goal

Prove the first interference theorem:

```text
in a forward pair comparison state,
the right positive center cannot be exactly the successor of the left center
```

## Implemented

Added the following theorems in
`DkMath.Collatz.PetalBridge.PressureState`:

```lean
SourcePressureForwardPairComparisonState.not_right_val_eq_left_succ
SourcePressureForwardPairComparisonState.left_succ_lt_right_val
```

The first theorem uses the local pulse boundary signs:

```text
left center > 0
right previous <= 0
```

If `W'.val = W.val + 1`, then the right previous index coincides with the left
center index.  This would force the same margin value to be both positive and
nonpositive.

The second theorem combines:

```lean
h.val_lt
h.not_right_val_eq_left_succ
```

with `omega`.

## What This Shows

This is stronger than distinctness.

Before this checkpoint, the forward pair gave:

```text
W.val < W'.val
```

Now it gives:

```text
W.val + 1 < W'.val
```

So two positive centers in an `FPC` branch cannot be adjacent.  There must be at
least one value slot between them.

In local-pulse language:

```text
positive center
nonpositive next / previous boundary
positive center
```

cannot collapse into adjacent centers.  The boundary sign pattern enforces a
real gap.

## Guardrails

This checkpoint proves a local interference fact for the explicit forward pair.

It does not assert:

- global spacing for all centers;
- uniqueness of centers;
- non-overlap of all pulse windows;
- absence of other witnesses between unrelated pairs;
- global coverage;
- Collatz convergence.

The pair-overlap obstruction branch remains separate.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
```

The final gate for this checkpoint also runs:

```text
lake build DkMath.Collatz.PetalBridge
git diff --check
```

## Next Branch Prediction

The next useful theorem is the index-level form:

```text
r + W.val + 1 < r + W'.val
```

or, equivalently, the right center is strictly beyond the left center's next
boundary.  That would make the pulse-window separation usable directly in
margin-index proofs.
