# Report: petal-276

## Goal

Add a compact left-next interference surface for the next local
window-comparison layer.

## Implemented

Added:

- `SourcePressureForwardPairComparisonState.left_next_interference_surface`

This theorem projects from:

- `SourcePressureForwardPairComparisonState.indexed_boundary_gap_surface`

## Established Fact

For any concrete forward pair comparison state

```lean
h : SourcePressureForwardPairComparisonState L W W'
```

Lean now exposes the compact surface:

```lean
0 < SourcePressureMarginInt n k (r + W.val)
  ∧ SourcePressureMarginInt n k (r + W.val + 1) <= 0
  ∧ 0 < SourcePressureMarginInt n k (r + W'.val)
  ∧ r + W.val + 1 < r + W'.val
```

## What Can Be Concluded

This fixes a reusable local interference pattern:

- the left center is positive;
- the immediate next index after the left center is nonpositive;
- the right center is positive;
- the left next index is strictly before the right center.

Thus a forward pair comparison cannot place the right positive center at the
left center's immediate successor.  The local window has already dropped to a
nonpositive boundary before the right positive center appears.

## Guardrails

This is still a local theorem for an explicit forward pair comparison state.
It does not assert global coverage, global uniqueness of positive centers,
arbitrary window disjointness, or Collatz termination.

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

## Next Branch Prediction

The next natural layer can either:

- name a dedicated left-next interference predicate, or
- add symmetric right-side projections if a caller starts needing them.

For now this compact theorem is probably enough for downstream local
window-comparison proofs.
