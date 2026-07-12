# Report: petal-280

## Goal

Add branch-specific projections from
`SourcePressureForwardPairComparisonState.boundary_corridor_surface_eq_or_lt`.

## Implemented

Added two thin projection theorems in
`DkMath.Collatz.PetalBridge.PressureState`:

- `SourcePressureForwardPairComparisonState.contact_corridor_shared_nonpos`
- `SourcePressureForwardPairComparisonState.strict_gap_corridor_endpoints_nonpos`

## Established Facts

For any
`h : SourcePressureForwardPairComparisonState L W W'`, the contact branch

```lean
r + W.val + 1 = r + (W'.val - 1)
```

projects the two syntactic endpoint signs:

```lean
SourcePressureMarginInt n k (r + W.val + 1) <= 0
  ∧ SourcePressureMarginInt n k (r + (W'.val - 1)) <= 0
```

The strict-gap branch

```lean
r + W.val + 1 < r + (W'.val - 1)
```

projects both endpoint signs and preserves the strict order:

```lean
SourcePressureMarginInt n k (r + W.val + 1) <= 0
  ∧ SourcePressureMarginInt n k (r + (W'.val - 1)) <= 0
  ∧ r + W.val + 1 < r + (W'.val - 1)
```

## What Can Be Concluded

The corridor split now has branch-specific caller-facing surfaces:

- contact branch: the shared corridor boundary is nonpositive under both
  endpoint expressions;
- strict-gap branch: both corridor endpoints are nonpositive and strictly
  ordered.

This is enough for downstream callers to branch without reopening
`boundary_corridor_surface_eq_or_lt`.

## Guardrails

These theorems are endpoint-only projections.  They do not prove that every
interior index of a strict corridor is nonpositive.

They also do not assert global coverage, uniqueness, arbitrary window
disjointness, or Collatz termination.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
```

Final gate:

```text
git diff --check
```

## Next Branch Prediction

The next branch should be driven by caller demand.  Natural small follow-ups are:

- contact branch: rewrite the right previous boundary sign through the contact
  equality;
- strict-gap branch: introduce a named `BoundaryStrictGapCorridor` predicate
  only if repeated callers need to carry this package.
