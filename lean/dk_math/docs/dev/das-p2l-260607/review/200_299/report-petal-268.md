# Report: petal-268

## Goal

Add the boundary-sign pair surface for
`SourcePressureForwardPairComparisonState`.

Target surface:

```text
FPC
  -> left local pulse signs
  -> right local pulse signs
  -> left center before right center
```

## Implemented

Added the following theorem in
`DkMath.Collatz.PetalBridge.PressureState`:

```lean
SourcePressureForwardPairComparisonState.boundary_sign_pair_surface
```

The proof uses:

```lean
h.left_signs
h.right_signs
h.val_lt
```

## Meaning

The forward pair-comparison branch now exposes both endpoints as ordered local
pulses:

```text
left previous <= 0
left center > 0
left next <= 0
right previous <= 0
right center > 0
right next <= 0
W.val < W'.val
```

This complements `center_pair_surface`.  The center theorem gives the compact
positive-center/target payload; this theorem gives the surrounding boundary
signs needed for pulse-shape comparison.

## Guardrails

This checkpoint is local to the explicit `FPC` pair.

It does not assert:

- uniqueness of local pulses;
- absence of other positive centers;
- global non-overlap;
- overlap repair;
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

The next natural branch is to make a full pulse-pair surface that combines:

```text
boundary_sign_pair_surface
center_pair_surface
adjacentPair
```

However, this may be redundant unless a caller needs all three at once.  A more
useful next step may be the first theorem that compares the two local pulse
windows using the boundary signs and strict value order.
