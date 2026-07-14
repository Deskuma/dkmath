# Report: petal-252

## Goal

Package `SourcePressureOrientedNeighborDiagnosticState` into a two-endpoint
box state.

## Implemented

Added in `DkMath.Collatz.PetalBridge.PressureState`:

```lean
def SourcePressureOrientedNeighborBoxState
theorem sourcePressureOrientedNeighborDiagnosticState_to_boxState
```

The new box state packages:

```text
OrientedNeighborDiagnosticState L W W'
+ CenteredLocalPulseBox W
+ CenteredLocalPulseBox W'
```

Each endpoint box carries:

- the previous/center/next margin sign pattern,
- margin-height bounds at previous, center, and next depths,
- net-drop bounds at the entry and exit adjacent edges.

## Design Choice

The definition reuses the existing one-endpoint contract:

```lean
SourcePressureBeamCenteredLocalPulseBox
```

instead of duplicating every bound inline.  This keeps the authoritative
one-endpoint box API in one place.  If the one-endpoint pulse-box contract is
refined later, the two-endpoint state follows it automatically.

## Proof Shape

The constructor theorem uses:

```lean
sourcePressureOrientedNeighborDiagnosticState_left_center_margin_signs
sourcePressureOrientedNeighborDiagnosticState_right_center_margin_signs
sourcePressureMarginInt_bounds_window
sourcePressureNetDropInt_bounds_window
```

Membership of `W` and `W'` is projected from the stored adjacent-pair-in-list
orientation.

## Guardrails

This is still only a local two-endpoint package.  It does not add:

- transport or propagation,
- list-wide coverage,
- aggregation,
- canonical witness selection,
- overlap repair,
- convergence or Collatz termination.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```

