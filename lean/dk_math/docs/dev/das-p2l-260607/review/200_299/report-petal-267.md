# Report: petal-267

## Goal

Bundle the two FPC center comparison facts into one caller-facing theorem.

Target surface:

```text
FPC
  -> two positive centers
  -> two addressed targets
  -> strict ordered centers
```

## Implemented

Added the following theorem in
`DkMath.Collatz.PetalBridge.PressureState`:

```lean
SourcePressureForwardPairComparisonState.center_pair_surface
```

The proof bundles the two existing pair-comparison facts:

```lean
h.center_pos_pair
h.center_targets_pair
```

## Meaning

The forward pair-comparison branch now has a compact caller-facing theorem:

```text
0 < margin(W.center)
0 < margin(W'.center)
Target(W.val)
Target(W'.val)
W.val < W'.val
```

This lets downstream comparison lemmas consume the positive-center and
addressed-target payload without repeatedly unpacking the two smaller
projection theorems.

## Guardrails

This checkpoint is still local to the explicit `FPC` pair.

It does not assert:

- uniqueness of center pulses;
- absence of other positive centers;
- propagation between endpoints;
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

The next natural branch is to expose the boundary-sign comparison surface for
both endpoints:

```text
previous <= 0
center > 0
next <= 0
```

Candidate theorem:

```lean
SourcePressureForwardPairComparisonState.boundary_sign_pair_surface
```

This would let the pair-comparison layer read both endpoints as ordered local
pulses with nonpositive neighboring margins and positive centers.
