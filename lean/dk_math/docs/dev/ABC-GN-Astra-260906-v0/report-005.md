# LUNA-005 — cubic 3/8 realized-fiber transfer

## Result

LUNA-005 is implemented.  A realized canonical cubic large profile now has a
positive exact-fiber witness, so the existing target `3/8` boundary theorem
transfers to the realized profile and its joint modulus.  Summing those
profile inequalities reduces the realized large contribution to a moment of
the actual joint moduli.

No estimate for that modulus moment was attempted.

## Files changed

- `DkMath/ABC/GNExcessCubicRealizedBoundary.lean` — new production module.
- `DkMath/ABC.lean` — imports the module immediately after
  `GNExcessRealizedMoment`.
- `README.md` and `ROADMAP.md` — record the completed LUNA-005 checkpoint.
- This report.

## Declarations added

The module provides:

- `GNExcessRealizedLargeProfileSpace_exists_positive_point`.
- `GNExcess_cubic_realizedLarge_boundaryWeight_le_modulus_three_eighths`.
- `GNExcess_cubic_realizedLarge_fiberMoment_le_modulus_three_eighths`.
- `GNExcessCubicRealizedLargeModulusMoment`.
- `GNExcessRealizedLargeBoundaryProfileSum_cubic_three_eighths_le_modulusMoment`.
- `GNExcess_cubic_realizedLarge_modulus_rpow_le_height_rpow`.
- `exp_GNExcessMassAt_sum_cubic_three_eighths_le_finiteEuler_add_modulusMoment`.

The earlier raw rectangular-profile theorems were left unchanged.

## Positive witness

The helper extracts a point from the exact realized fiber.  If that point were
zero, the target modulus identity reduces its modulus to
`GNNonExceptionalRepeatedPart 3 0 1`.  The cubic value at zero is `3`, while
the non-exceptional support excludes its only prime divisor, so the repeated
part is `1`.  This contradicts the strict large-modulus condition
`X + 1 < modulus`.

## Profile and fiber transfer

The profile theorem invokes the existing
`GNExcess_cubic_target_boundaryWeight_le_repeatedPart_three_eighths` at the
positive witness, rewrites the target profile to the arbitrary realized
profile, and uses
`GNExcessJointDepthModulus_target_eq_repeatedPart` to replace repeated part by
the profile joint modulus.

The preferred semantic fiber theorem was also added.  It combines
`card_GNExactExcessProfileEvent_le_largeBoundary` with the profile theorem, so
the actual fiber cardinality times its exponential weight satisfies the same
modulus bound.

## Modulus moment and aggregate bridge

`GNExcessCubicRealizedLargeModulusMoment X` is the finite sum of
`M(e)^(3/8)` over the realized canonical cubic large-profile space.  A direct
`Finset.sum_le_sum` proves

```text
GNExcessRealizedLargeBoundaryProfileSum(..., 3/8)
  ≤ GNExcessCubicRealizedLargeModulusMoment X.
```

The final theorem composes this inequality with
`exp_GNExcessMassAt_sum_le_finiteEuler_add_realizedLarge_cubic`, yielding the
finite-Euler term plus the realized joint-modulus moment.  The height
diagnostic corollary also records
`M(e)^(3/8) ≤ (3 * (X + 1)^2)^(3/8)` pointwise; it is not an aggregate bound.

## Verification

From `lean/dk_math`:

```bash
lake build DkMath.ABC.GNExcessCubicRealizedBoundary
lake build DkMath.ABC
```

Both builds completed successfully.  The focused module build completed 8786
jobs and the ABC aggregator build completed 8843 jobs.  The existing warning
at `DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147:6` is unrelated
to this checkpoint.

The changed Lean files contain no `sorry`, `admit`, or new `axiom`, and no
reference to `abc_main_axiom`.  `#print axioms` on the positive-witness,
profile, fiber, aggregate, and final bridge theorems reports only

```text
propext, Classical.choice, Quot.sound
```

## Remaining mathematical blocker

The large-boundary problem is now the global arithmetic control of

```text
∑ e ∈ realized large profiles, M(e)^(3/8).
```

No bound, profile count, density theorem, paired-orientation argument, or ABC
quality coupling is asserted here.  The next research question is how the
distinct realized joint moduli are constrained strongly enough to control this
aggregate.
