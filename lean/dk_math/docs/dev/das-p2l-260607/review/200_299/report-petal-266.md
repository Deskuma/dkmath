# Report: petal-266

## Goal

Add the first actual pair-comparison facts from
`SourcePressureForwardPairComparisonState`.

Target surface:

```text
FPC
  -> left center positive
  -> right center positive
  -> both addressed targets
  -> W.val < W'.val
```

## Implemented

Added the following theorems in
`DkMath.Collatz.PetalBridge.PressureState`:

```lean
SourcePressureForwardPairComparisonState.center_pos_pair
SourcePressureForwardPairComparisonState.center_targets_pair
```

The proofs use:

```lean
h.left_signs
h.right_signs
h.val_lt
```

## Meaning

The forward pair-comparison state now has its first direct comparison facts.

The two endpoints are not merely boxed and adjacent.  The forward branch now
explicitly exposes:

- the left center margin is positive;
- the right center margin is positive;
- the left endpoint is an addressed beam target;
- the right endpoint is an addressed beam target;
- the left endpoint value is strictly before the right endpoint value.

This is the first real pair-comparison surface.  It turns the previous
projection layer into a compact theorem interface for comparing the two
positive centers.

## Guardrails

This checkpoint remains local to the explicit `FPC` witness pair.

It does not assert:

- propagation from one endpoint to the other;
- uniqueness of positive centers;
- absence of all other centers;
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

The next natural branch is to bundle the two comparison facts into a single
caller-facing theorem if downstream proofs repeatedly need both:

```lean
theorem SourcePressureForwardPairComparisonState.center_pair_surface
```

Candidate payload:

```text
0 < margin(W.center)
0 < margin(W'.center)
Target(W.val)
Target(W'.val)
W.val < W'.val
```

If callers need finer control, keep the current two-theorem surface and proceed
directly to comparing the left/right pulse boxes by their signed boundary
patterns.
