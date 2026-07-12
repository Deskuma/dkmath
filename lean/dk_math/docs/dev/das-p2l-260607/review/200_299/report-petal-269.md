# Report: petal-269

## Goal

Add index-level center order consequences from
`SourcePressureForwardPairComparisonState`.

Target surface:

```text
FPC
  -> W.val < W'.val
  -> r + W.val < r + W'.val
  -> center indices are distinct
```

## Implemented

Added the following theorems in
`DkMath.Collatz.PetalBridge.PressureState`:

```lean
SourcePressureForwardPairComparisonState.center_index_lt
SourcePressureForwardPairComparisonState.center_index_ne
```

The first theorem uses `h.val_lt` and `omega`.  The second theorem is a direct
`ne_of_lt` projection from the strict index order.

## Meaning

The forward pair-comparison branch now descends from witness-value order to the
actual center indices used by `SourcePressureMarginInt`.

This is useful because boundary and center facts are stated at indices such as:

```text
r + (W.val - 1)
r + W.val
r + W.val + 1
```

The new theorems make the center-index separation explicit before later
comparison lemmas combine it with boundary-sign surfaces.

## Guardrails

This checkpoint only transports an already proved local value order through
addition by `r`.

It does not assert:

- a minimum gap larger than one;
- non-overlap of the full pulse windows;
- uniqueness of positive centers;
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

The next natural branch is to combine index separation with the boundary-sign
surface:

```text
boundary_sign_pair_surface
center_index_lt
center_index_ne
```

This should support the first interference/adjacency reading theorem for two
positive pulse centers.
