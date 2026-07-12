# Report: petal-265

## Goal

Add caller-facing projections from
`SourcePressureForwardPairComparisonState`.

Target projections:

```text
FPC
  -> left endpoint membership
  -> right endpoint membership
  -> left endpoint sign-and-target surface
  -> right endpoint sign-and-target surface
```

## Implemented

Added the following theorems in
`DkMath.Collatz.PetalBridge.PressureState`:

```lean
SourcePressureForwardPairComparisonState.left_mem
SourcePressureForwardPairComparisonState.right_mem
SourcePressureForwardPairComparisonState.left_signs
SourcePressureForwardPairComparisonState.right_signs
```

The proofs are thin projections through the endpoint pulse boxes:

```lean
h.left_box.signs
h.right_box.signs
```

## Meaning

The forward pair-comparison state now exposes the immediate diagnostic payload
that comparison callers need:

```text
FPC
  -> left signs
  -> right signs
  -> W.val < W'.val
  -> adjacent pair
```

This avoids making downstream pair-comparison lemmas manually unpack:

```text
FPC -> left_box/right_box -> SourcePressureBeamCenteredLocalPulseBox.signs
```

## Guardrails

This checkpoint is projection-only.

It does not assert:

- propagation between endpoints;
- endpoint uniqueness beyond already proved forward order;
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

The next natural branch is to expose comparison-ready bundled signs:

```lean
theorem SourcePressureForwardPairComparisonState.endpoint_signs
```

or to move directly into the first comparison theorem:

```text
FPC
  -> left center positive
  -> right center positive
  -> W.val < W'.val
```

The latter is likely more useful: it starts the actual pair-comparison layer
while still relying only on explicit local witness data.
