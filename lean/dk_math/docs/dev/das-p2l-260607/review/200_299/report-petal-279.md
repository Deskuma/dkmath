# Report: petal-279

## Goal

Bundle the boundary corridor signs with the contact-or-gap split.

## Implemented

Added:

- `SourcePressureForwardPairComparisonState.boundary_corridor_surface_eq_or_lt`

This theorem combines:

- `SourcePressureForwardPairComparisonState.boundary_corridor_surface`
- `SourcePressureForwardPairComparisonState.boundary_corridor_eq_or_lt`

## Established Fact

For any concrete forward pair comparison state

```lean
h : SourcePressureForwardPairComparisonState L W W'
```

Lean now proves:

```lean
SourcePressureMarginInt n k (r + W.val + 1) <= 0
  ∧ SourcePressureMarginInt n k (r + (W'.val - 1)) <= 0
  ∧ (r + W.val + 1 = r + (W'.val - 1)
      ∨ r + W.val + 1 < r + (W'.val - 1))
```

## What Can Be Concluded

The boundary corridor between a forward pair's two positive centers is now
available as one sign-bundled dichotomy:

- both corridor endpoints are nonpositive;
- either those endpoints coincide, giving a contact corridor;
- or the left endpoint lies strictly before the right endpoint, giving a
  genuine gap corridor.

This is a stronger caller-facing surface than the plain arithmetic split,
because the nonpositive endpoint signs are carried through the same theorem.

## Guardrails

This still does not say every interior point of a strict corridor is
nonpositive.  It also does not assert global coverage, uniqueness of all
positive centers, arbitrary window disjointness, or Collatz termination.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
```

Final whitespace gate:

```text
git diff --check
```

## Next Branch Prediction

The next theorem should probably be added only if a caller needs it:

- contact-case projection: shared nonpositive boundary;
- strict-gap projection: two ordered nonpositive endpoints.

For now, `boundary_corridor_surface_eq_or_lt` is the compact branch point.
