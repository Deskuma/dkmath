# Report: petal-286

## Goal

Continue from the center/separator/center surface toward finite-window packing
bounds by creating the first finite-window carrier.

## Implemented

Added:

- `SourcePressureFiniteWindowPackingSeparatorState`

Added projections and constructor:

- `SourcePressureFiniteWindowPackingSeparatorState.localPacking`
- `SourcePressureFiniteWindowPackingSeparatorState.left_center_in_window`
- `SourcePressureFiniteWindowPackingSeparatorState.right_center_in_window`
- `SourcePressureFiniteWindowPackingSeparatorState.separator_in_window`
- `SourcePressureFiniteWindowPackingSeparatorState.center_separator_surface`
- `SourcePressureFiniteWindowPackingSeparatorState.two_le_value_gap`
- `SourcePressureFiniteWindowPackingSeparatorState.two_le_index_gap`
- `SourcePressureLocalPackingSeparatorState.to_finiteWindowPackingSeparatorState`

Added upstream finite-window lifted split theorems:

- `sourcePressureFailureResolutionState_to_finiteWindowPackingSeparatorState_or_pairOverlap`
- `sourcePressureSortedFailureState_to_finiteWindowPackingSeparatorState_or_pairOverlap`
- `sourcePressureBeamSeedState_to_finiteWindowPackingSeparatorState_or_pairOverlap`

## Established Facts

The finite-window state stores a local packing separator and records that both
positive center indices lie in `[lo, hi]`:

```lean
SourcePressureLocalPackingSeparatorState L W W' m
  ∧ lo <= r + W.val
  ∧ r + W'.val <= hi
```

Lean proves the separator is also inside the same window:

```lean
lo <= m ∧ m <= hi
```

This follows from:

```text
lo <= left center < separator < right center <= hi
```

## Upstream Route

With explicit list-wide window bounds

```lean
hlo_all : ∀ W, W ∈ L → lo <= r + W.val
hhi_all : ∀ W, W ∈ L → r + W.val <= hi
```

the state ladder now reaches the finite-window carrier:

```text
FailureResolution + sorted(L)
  -> FiniteWindowPackingSeparatorState
   ∨ concrete adjacent-pair overlap obstruction

SortedFailure + sorted(L)
  -> FiniteWindowPackingSeparatorState
   ∨ concrete adjacent-pair overlap obstruction

BeamSeed + sorted(L)
  -> FiniteWindowPackingSeparatorState
   ∨ concrete adjacent-pair overlap obstruction
```

## What Can Be Concluded

The route has advanced from a raw local sign pattern to a finite-window carrier:

```text
LocalPackingSeparatorState
  -> center/separator/center surface
  -> finite-window carrier
  -> separator is inside the same finite window
  -> prepares positive-center packing bounds
  -> local Big
```

The key new fact is that once both positive centers are inside an explicit
window, the certified nonpositive separator is also inside that window.

## Guardrails

This checkpoint does not count centers yet.  It also does not claim:

- global coverage;
- arbitrary disjointness of windows;
- maximality of the window;
- global termination.

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

The next layer should define a finite-window surface bundling:

```text
left center positive and in window
separator nonpositive and in window
right center positive and in window
two-step spacing
```

This should be added before attempting any actual counting theorem.
