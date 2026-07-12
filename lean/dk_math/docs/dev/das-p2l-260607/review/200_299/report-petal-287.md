# Report: petal-287

## Goal

Expose the finite-window sign pattern carried by
`SourcePressureFiniteWindowPackingSeparatorState`, then lift that surface
through the failure-resolution state ladder.

## Implemented

Added the requested finite-window surface:

- `SourcePressureFiniteWindowPackingSeparatorState.window_center_separator_surface`

It exposes, in one theorem:

```text
positive left center in the window
  -> nonpositive separator in the window
  -> positive right center in the window
  -> two-step center spacing
```

Added the three upstream lifted splits:

- `sourcePressureFailureResolutionState_to_windowCenterSeparatorSurface_or_pairOverlap`
- `sourcePressureSortedFailureState_to_windowCenterSeparatorSurface_or_pairOverlap`
- `sourcePressureBeamSeedState_to_windowCenterSeparatorSurface_or_pairOverlap`

Each state now reaches either the explicit finite-window sign surface or a
concrete adjacent-pair overlap obstruction.

## Additional Results

Added two counting-facing consequences:

- `SourcePressureFiniteWindowPackingSeparatorState.window_order_chain`
- `SourcePressureFiniteWindowPackingSeparatorState.two_le_window_width`

The order-chain theorem fixes the exact index geometry:

```text
lo <= left center < separator < right center <= hi
```

Consequently Lean proves:

```lean
lo + 2 <= hi
```

Thus any finite window carrying this state contains at least three distinct
ordered indices and has width at least two.

## Established Facts

For every selected forward pair represented by the finite-window carrier:

1. Both centers have positive pressure margin.
2. An explicit separator between them has nonpositive pressure margin.
3. All three indices lie in the same explicit finite window.
4. The centers are separated by at least two value steps.
5. The window itself must have width at least two.

These are theorem-level facts checked by Lean.  They are the local packing
contract needed before finite-family counting begins.

## State Route

```text
FiniteWindowPackingSeparatorState
  -> in-window positive / nonpositive / positive surface
  -> strict in-window order chain
  -> each selected positive-center pair consumes a separator position
  -> finite-window positive-center packing input
  -> local Big
```

The upstream route is now:

```text
FailureResolution / SortedFailure / BeamSeed + sorted(L) + window bounds
  -> window center/separator/center surface
   | concrete adjacent-pair overlap obstruction
```

## Counting Boundary

The next genuine counting theorem requires a finite family of selected pairs.
To turn the local result into a cardinality inequality, the implementation must
control reuse of separator indices across that family.  The smallest useful
next invariant is therefore one of:

- injectivity of the chosen separator as a function of an ordered pair;
- disjointness of the open center intervals of selected pairs; or
- a bounded-multiplicity theorem for separator reuse.

Once one of these is available, the present order-chain theorem can feed a
finite cardinality bound directly.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```

No `sorry` was introduced in the Wall/pressure state work.

## Next Branch Prediction

Introduce a finite selected-pair family and determine the weakest provable
separator-reuse invariant.  Prefer bounded multiplicity if injectivity is too
strong; the local theorem already supplies every pair with an in-window
nonpositive separator.
