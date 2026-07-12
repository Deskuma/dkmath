# Report: petal-284

## Goal

Package the local nonpositive separator into a named local packing state and
lift the upstream BeamSeed / SortedFailure / FailureResolution routes to that
state.

The focus is the observed local phenomenon itself: positive centers carried by
the forward pair state cannot be packed without a certified nonpositive
separator between them.

## Implemented

Added the named state:

- `SourcePressureLocalPackingSeparatorState`

Added projections:

- `SourcePressureLocalPackingSeparatorState.forward`
- `SourcePressureLocalPackingSeparatorState.left_lt_separator`
- `SourcePressureLocalPackingSeparatorState.separator_lt_right`
- `SourcePressureLocalPackingSeparatorState.separator_nonpos`
- `SourcePressureLocalPackingSeparatorState.two_le_value_gap`
- `SourcePressureLocalPackingSeparatorState.two_le_index_gap`

Added constructor:

- `SourcePressureForwardPairComparisonState.to_localPackingSeparatorState`

Added upstream named-state split theorems:

- `sourcePressureFailureResolutionState_to_localPackingSeparatorState_or_pairOverlap`
- `sourcePressureSortedFailureState_to_localPackingSeparatorState_or_pairOverlap`
- `sourcePressureBeamSeedState_to_localPackingSeparatorState_or_pairOverlap`

## Established Facts

The named state records:

```lean
SourcePressureForwardPairComparisonState L W W'
  ∧ r + W.val < m
  ∧ m < r + W'.val
  ∧ SourcePressureMarginInt n k m <= 0
```

From this state, Lean can project both local spacing facts:

```lean
W.val + 2 <= W'.val
r + W.val + 2 <= r + W'.val
```

Every `SourcePressureForwardPairComparisonState L W W'` produces such a named
separator state:

```lean
∃ m, SourcePressureLocalPackingSeparatorState L W W' m
```

## Upstream Route

The state ladder now reaches the named local packing state:

```text
FailureResolution + sorted(L)
  -> LocalPackingSeparatorState
   ∨ concrete adjacent-pair overlap obstruction

SortedFailure + sorted(L)
  -> LocalPackingSeparatorState
   ∨ concrete adjacent-pair overlap obstruction

BeamSeed + sorted(L)
  -> LocalPackingSeparatorState
   ∨ concrete adjacent-pair overlap obstruction
```

## What Can Be Concluded

This checkpoint turns the previous raw separator theorem into a reusable local
packing obstruction.

The observed structure is now:

```text
FPC corridor
  -> nonpositive separator
  -> LocalPackingSeparatorState
  -> upstream seed/failure split
  -> reusable local packing obstruction toward local Big
```

This is a local theorem about explicit witness lists and margin signs.  It does
not need to refer to any external named conjecture.

## Guardrails

This checkpoint does not claim global termination.  It also does not claim:

- global positive-center uniqueness;
- arbitrary window disjointness;
- global coverage of all possible centers;
- nonpositivity of every interior point of a strict corridor.

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

The next reusable layer is likely one of:

- a compact `LocalPackingSeparatorState.center_surface` projection containing
  left positive center, nonpositive separator, right positive center;
- a finite-list aggregation step that counts or indexes repeated local packing
  separators without claiming global coverage.

The first is cheaper and should be preferred unless a real aggregation caller is
ready.
