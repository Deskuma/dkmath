# Report: petal-270

## Goal

Bundle boundary signs with index-level center order.

Target surface:

```text
FPC
  -> left local pulse signs
  -> right local pulse signs
  -> r + W.val < r + W'.val
```

## Implemented

Added the following theorem in
`DkMath.Collatz.PetalBridge.PressureState`:

```lean
SourcePressureForwardPairComparisonState.indexed_boundary_pair_surface
```

The proof combines:

```lean
h.boundary_sign_pair_surface
h.center_index_lt
```

## Meaning

The forward pair-comparison branch now has a boundary-sign surface stated in
the same index language as `SourcePressureMarginInt`.

The theorem exposes:

```text
left previous <= 0
left center > 0
left next <= 0
right previous <= 0
right center > 0
right next <= 0
r + W.val < r + W'.val
```

This is the comparison-ready version of the two local pulse windows.  It avoids
forcing downstream callers to translate `W.val < W'.val` into center-index
order each time.

## Guardrails

This checkpoint only rebundles already proved local facts.

It does not assert:

- a minimum distance between the two center indices beyond strict order;
- non-overlap of the whole pulse windows;
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

The next natural branch is to derive a compact noncoincidence theorem for the
two positive center indices together with their boundary signs:

```text
indexed_boundary_pair_surface
center_index_ne
```

If more useful for callers, this can be phrased as a named two-center
separation surface before moving into interference/overlap comparisons.
