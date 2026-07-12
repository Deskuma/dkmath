# Report: petal-282

## Goal

Keep `SourcePressureForwardPairComparisonState.right_value_corridor_surface`
as the preferred public value-level corridor surface, and add only thin
branch-specific projections if needed by downstream callers.

## Implemented

Added two endpoint-only branch projections:

- `SourcePressureForwardPairComparisonState.contact_value_corridor_surface`
- `SourcePressureForwardPairComparisonState.strict_gap_value_corridor_surface`

Both theorems consume existing corridor branch data and avoid adding any new
global or interior-corridor claim.

## Established Facts

In the contact branch

```lean
r + W.val + 1 = r + (W'.val - 1)
```

Lean proves:

```lean
SourcePressureMarginInt n k (r + W.val + 1) <= 0
  ∧ SourcePressureMarginInt n k (r + (W'.val - 1)) <= 0
  ∧ W'.val = W.val + 2
```

In the strict-gap branch

```lean
r + W.val + 1 < r + (W'.val - 1)
```

Lean proves:

```lean
SourcePressureMarginInt n k (r + W.val + 1) <= 0
  ∧ SourcePressureMarginInt n k (r + (W'.val - 1)) <= 0
  ∧ W.val + 2 < W'.val
```

## What Can Be Concluded

The public theorem `right_value_corridor_surface` remains the compact default:

```lean
endpoint signs
  ∧ (W'.val = W.val + 2 ∨ W.val + 2 < W'.val)
```

When a caller has already selected a branch, the new theorems provide the
corresponding value-level consequence directly.

## Guardrails

These are local forward-pair comparison facts only.  They do not prove:

- all interior indices of a strict corridor are nonpositive;
- global uniqueness of positive centers;
- arbitrary window disjointness;
- Collatz termination.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
```

Final gate:

```text
lake build DkMath.Collatz.PetalBridge
git diff --check
```

## Next Branch Prediction

The corridor layer is now sufficiently surfaced for both compact and
branch-specific callers.  The next useful work should start from a concrete
consumer of these value gaps, rather than extending the corridor API further.
