# Report: petal-275

## Goal

Add compact projections from `indexed_boundary_gap_surface` for the next
window-interference layer.

## Implemented

Added two projection theorems:

- `SourcePressureForwardPairComparisonState.left_next_boundary_before_right_center`
- `SourcePressureForwardPairComparisonState.left_next_boundary_nonpos_and_before_right_center`

Both project from:

- `SourcePressureForwardPairComparisonState.indexed_boundary_gap_surface`

## Established Fact

For any concrete forward pair comparison state

```lean
h : SourcePressureForwardPairComparisonState L W W'
```

Lean now exposes the following facts directly:

```lean
r + W.val + 1 < r + W'.val
```

and:

```lean
SourcePressureMarginInt n k (r + W.val + 1) <= 0
  ∧ r + W.val + 1 < r + W'.val
```

The second theorem is the more useful caller-facing projection: it says the
left next boundary is already nonpositive and still strictly before the right
positive center.

## What Can Be Concluded

The forward pair comparison state now gives a compact local obstruction against
immediate center contact:

- the left center is positive;
- its next boundary is nonpositive;
- that next boundary is strictly before the right positive center.

So the local pulse cannot move directly from the left positive center to the
right positive center at the immediate successor index.  There is an index-level
gap between the left next boundary and the right center.

## Guardrails

This remains a local statement about a chosen forward pair comparison state.
It does not claim global coverage, uniqueness of all centers, full window
disjointness for arbitrary witnesses, or Collatz convergence.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
```

The final whitespace gate is:

```text
git diff --check
```

## Next Branch Prediction

The next natural step is to name a slightly richer interference state, perhaps
one that combines:

- left center positivity;
- left next boundary nonpositivity;
- right center positivity;
- `left next boundary < right center`.

That would give the next layer a single input theorem for local window
interference without destructuring the full boundary surface.
