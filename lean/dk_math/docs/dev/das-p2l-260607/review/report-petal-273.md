# Report: petal-273

## Goal

Add the index-level form of the first interference theorem for
`SourcePressureForwardPairComparisonState`.

## Implemented

Added two caller-facing theorems in
`DkMath.Collatz.PetalBridge.PressureState`:

- `SourcePressureForwardPairComparisonState.left_next_index_lt_right_center_index`
- `SourcePressureForwardPairComparisonState.left_next_boundary_lt_right_center_index`

Both are direct index-level consequences of the established value-level theorem:

- `SourcePressureForwardPairComparisonState.left_succ_lt_right_val`

The proof is intentionally thin:

```lean
have hgap : W.val + 1 < W'.val := h.left_succ_lt_right_val
omega
```

## Established Fact

For any forward pair comparison state `h : SourcePressureForwardPairComparisonState L W W'`,
Lean now proves:

```lean
r + W.val + 1 < r + W'.val
```

and the syntactic variant:

```lean
r + (W.val + 1) < r + W'.val
```

This means the right positive center is strictly beyond the left center's next
boundary index.  The previous checkpoint proved this at the witness-value level;
this checkpoint fixes the same fact at the exact index layer used by
`SourcePressureMarginInt`.

## What This Rules Out

Within a concrete `SourcePressureForwardPairComparisonState`:

- the right center cannot be equal to the successor of the left center;
- the left center's next index is strictly before the right center index;
- the two local pulse centers are separated by at least one index-level gap.

## Guardrails

This is a local theorem about an explicit forward pair comparison state.
It does not claim:

- global uniqueness of positive centers;
- global coverage of all candidate addresses;
- full non-overlap of complete windows beyond the proved boundary-center inequality;
- Collatz convergence or termination.

The result is a stable local interference fact suitable for the next comparison
layer.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
```

The broader gate for this checkpoint is:

```text
lake build DkMath.Collatz.PetalBridge
git diff --check
```

## Next Branch Prediction

The next useful branch is to bundle this index-level separation with the already
available boundary sign surface:

```lean
SourcePressureForwardPairComparisonState.indexed_boundary_separation_surface
```

That would give downstream callers a single theorem containing:

- left boundary signs;
- right boundary signs;
- strict center-index separation;
- strict left-next-boundary-before-right-center separation.

This should help the pair-comparison layer reason about local pulse interference
without repeatedly reconstructing the same `omega` step.
