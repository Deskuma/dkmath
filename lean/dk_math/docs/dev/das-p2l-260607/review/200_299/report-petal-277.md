# Report: petal-277

## Goal

Relate the left next boundary to the right previous boundary in a forward pair
comparison state.

## Implemented

Added:

- `SourcePressureForwardPairComparisonState.left_next_boundary_le_right_previous_boundary`
- `SourcePressureForwardPairComparisonState.boundary_corridor_surface`

The first theorem is derived from:

- `SourcePressureForwardPairComparisonState.left_succ_lt_right_val`

The second theorem bundles signs from:

- `SourcePressureForwardPairComparisonState.indexed_boundary_gap_surface`

and the new corridor inequality.

## Established Fact

For any concrete forward pair comparison state

```lean
h : SourcePressureForwardPairComparisonState L W W'
```

Lean now proves the index corridor:

```lean
r + W.val + 1 <= r + (W'.val - 1)
```

and the sign-bundled version:

```lean
SourcePressureMarginInt n k (r + W.val + 1) <= 0
  ∧ SourcePressureMarginInt n k (r + (W'.val - 1)) <= 0
  ∧ r + W.val + 1 <= r + (W'.val - 1)
```

## What Can Be Concluded

The local forward pair has a nonpositive boundary corridor between the two
positive centers:

- the left next boundary is nonpositive;
- the right previous boundary is nonpositive;
- the left next boundary is no later than the right previous boundary.

This upgrades the earlier strict center separation into a boundary-to-boundary
corridor statement.  It is the first compact form saying that the region between
the two positive centers is bracketed by nonpositive boundary endpoints.

## Guardrails

This is local to an explicit forward pair comparison state.  It does not assert
that every index inside the corridor is nonpositive, nor does it prove global
coverage, global uniqueness, arbitrary window disjointness, or Collatz
termination.

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

The next useful branch is likely an explicit named corridor predicate, but only
if downstream proofs repeatedly need the three bundled facts.  For now,
`boundary_corridor_surface` is a sufficient compact theorem for local
window-comparison callers.
