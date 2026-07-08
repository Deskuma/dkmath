# Report: petal-281

## Goal

Stop expanding the corridor API itself and start a downstream caller theorem
that consumes the existing boundary corridor split.

## Implemented

Added:

- `SourcePressureForwardPairComparisonState.right_value_corridor_surface`

This theorem consumes
`SourcePressureForwardPairComparisonState.boundary_corridor_surface_eq_or_lt`
and exports the result at the witness-value level.

## Established Fact

For any
`h : SourcePressureForwardPairComparisonState L W W'`, Lean proves:

```lean
SourcePressureMarginInt n k (r + W.val + 1) <= 0
  ∧ SourcePressureMarginInt n k (r + (W'.val - 1)) <= 0
  ∧ (W'.val = W.val + 2 ∨ W.val + 2 < W'.val)
```

So a forward pair comparison has two nonpositive corridor endpoints, and the
right center is either exactly two value steps after the left center or is
strictly farther away.

## What Can Be Concluded

This is the first downstream caller-facing use of the corridor split.  The
index-level contact/gap branch now has a direct value-level reading:

- contact corresponds to the adjacent centers having value gap `2`;
- strict gap corresponds to the right center being more than two value steps
  after the left center.

## Guardrails

The theorem still only carries endpoint signs.  It does not prove:

- every interior index of a strict corridor is nonpositive;
- global positive-center uniqueness;
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

The next useful branch is to expose branch-specific value projections only if a
caller needs them:

- contact: `W'.val = W.val + 2` plus endpoint signs;
- strict gap: `W.val + 2 < W'.val` plus endpoint signs.

Until then, `right_value_corridor_surface` is the cleaner public surface.
