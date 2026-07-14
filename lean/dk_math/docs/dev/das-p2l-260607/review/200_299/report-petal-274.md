# Report: petal-274

## Goal

Bundle the boundary sign surface with the index-level gap produced by the first
interference theorem.

## Implemented

Added:

- `SourcePressureForwardPairComparisonState.indexed_boundary_gap_surface`

This theorem combines:

- `SourcePressureForwardPairComparisonState.indexed_boundary_separation_surface`
- `SourcePressureForwardPairComparisonState.left_next_index_lt_right_center_index`

## Established Fact

For any concrete forward pair comparison state

```lean
h : SourcePressureForwardPairComparisonState L W W'
```

Lean now proves the combined local surface:

```lean
SourcePressureMarginInt n k (r + (W.val - 1)) <= 0
0 < SourcePressureMarginInt n k (r + W.val)
SourcePressureMarginInt n k (r + W.val + 1) <= 0
SourcePressureMarginInt n k (r + (W'.val - 1)) <= 0
0 < SourcePressureMarginInt n k (r + W'.val)
SourcePressureMarginInt n k (r + W'.val + 1) <= 0
r + W.val < r + W'.val
r + W.val != r + W'.val
r + W.val + 1 < r + W'.val
```

The new piece is the final inequality:

```lean
r + W.val + 1 < r + W'.val
```

so downstream callers can use the left next boundary and the right positive
center separation without rebuilding the first interference theorem.

## What Can Be Concluded

In a `SourcePressureForwardPairComparisonState`, the two local pulse windows
carry their usual boundary sign pattern, and the right positive center is
strictly beyond the left center's next boundary index.

This is stronger than merely saying the center indices are distinct.  It says
that the immediate successor index of the left center is still strictly before
the right center.

## Guardrails

This remains a local theorem about an explicit forward pair comparison state.
It does not prove:

- global uniqueness of positive centers;
- global coverage of all witness candidates;
- complete non-overlap of arbitrary windows;
- Collatz termination or convergence.

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

The next useful theorem is probably a compact projection from
`indexed_boundary_gap_surface`, for example:

```lean
SourcePressureForwardPairComparisonState.left_next_boundary_before_right_center
```

or a pair-window interference surface that names the fact:

```text
left next boundary < right center
```

as a reusable obstruction against immediate contact between two forward pulse
centers.
