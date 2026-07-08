# Report: petal-285

## Goal

Expose the local sign pattern carried by
`SourcePressureLocalPackingSeparatorState`:

```text
positive center -> nonpositive separator -> positive center
```

This checkpoint moves the named packing separator state toward finite-window
packing bounds and local Big.

## Implemented

Added:

- `SourcePressureLocalPackingSeparatorState.center_separator_surface`

Added upstream lifted surface theorems:

- `sourcePressureFailureResolutionState_to_centerSeparatorSurface_or_pairOverlap`
- `sourcePressureSortedFailureState_to_centerSeparatorSurface_or_pairOverlap`
- `sourcePressureBeamSeedState_to_centerSeparatorSurface_or_pairOverlap`

## Established Facts

From a local packing separator state, Lean now projects:

```lean
0 < SourcePressureMarginInt n k (r + W.val)
  ∧ SourcePressureMarginInt n k m <= 0
  ∧ 0 < SourcePressureMarginInt n k (r + W'.val)
  ∧ r + W.val < m
  ∧ m < r + W'.val
  ∧ W.val + 2 <= W'.val
```

So the named state directly exposes:

```text
left positive center
  < nonpositive separator
  < right positive center
```

with a certified value gap of at least two.

## Upstream Route

The state ladder now reaches this center/separator/center surface:

```text
FailureResolution + sorted(L)
  -> center/separator/center surface
   ∨ concrete adjacent-pair overlap obstruction

SortedFailure + sorted(L)
  -> center/separator/center surface
   ∨ concrete adjacent-pair overlap obstruction

BeamSeed + sorted(L)
  -> center/separator/center surface
   ∨ concrete adjacent-pair overlap obstruction
```

## What Can Be Concluded

This is the next step in the route:

```text
observed local structure
  -> reusable local theorem
  -> finite-window packing bound
  -> local Big
```

The explicit local phenomenon is now theoremized: a forward pair of positive
centers carries a nonpositive separator strictly between them.  Upstream seed
and failure states either expose that pattern or return a concrete overlap
obstruction.

## Guardrails

This checkpoint is local to the explicit witness list `L`.  It does not claim:

- global coverage;
- global uniqueness of positive centers;
- arbitrary window disjointness;
- global termination.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```

## Next Branch Prediction

The next useful step is a finite-window carrier that stores:

```text
window bounds
left positive center in window
nonpositive separator in window
right positive center in window
```

Only after that should counting or packing-density theorems be attempted.
