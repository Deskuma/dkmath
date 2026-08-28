# DHNT Cosmic-square analytic scaling implementation report

## Scope and baseline

This report closes the Phase I acceptance set in
`CODEX-DHNT-COSMIC-SQUARE-ANALYTIC-SCALING-DIRECTIVE-260820.md`.  The
implementation started from checkpoint `98745b7c29d1fba9c7dfa3d18b734a29771f77c7`
and changes only the StructuralArithmetic bridge, aggregate, README, and this
report.  No DHNT base, FLT5, KUS, or analytic tower refactor was made.

## Implemented declarations

`CosmicSquareScaling.lean` provides:

- `cosmicSquareImage` and `cosmicSquareImage_pos` for the positive branch
  `sqrt (1 + y) - 1`;
- `cosmicSquareImage_add_one_sq` for its exact square reconstruction;
- the reusable positive-domain `rpow_log_ratio` theorem;
- `cosmicSquareScale` and
  `cosmicSquareImage_rpow_scale`, with hypotheses `0 < y` and `y ≠ 1`;
- the exact boundary theorems `cosmicSquareImage_three` and
  `cosmicSquareScale_three`;
- `dynamicPrimeCoordinates`, its pointwise/support preservation theorems, and
  the `y = 30` support corollary;
- `cosmicSquareImage_thirty`,
  `cosmicSquareScale_thirty_ne_zero`, and the exact symbolic reconstruction
  `thirty_rpow_cosmicSquareScale`.

The `y = 1` denominator boundary is handled by the explicit `y ≠ 1`
hypothesis in the reconstruction theorem.  At `y = 3`, the scale is exactly
zero, so Phase-H support preservation is intentionally not applied.  At
`y = 30`, reconstruction is symbolic (`sqrt 31 - 1`) and uses no decimal
approximation.

The dynamic vector is a radially scaled real-valued image of natural prime
valuation coordinates.  No theorem identifies it with a prime factorization
of a real number, with KUS transport, with PowerGauge projection, or with a
multiplicative map `y ↦ y ^ kappa(y)`.

## Verification

Focused builds completed successfully:

```text
lake build DkMath.NumberTheory.StructuralArithmetic.CosmicSquareScaling
lake build DkMath.NumberTheory.StructuralArithmetic.RadialScaling
lake build DkMath.NumberTheory.StructuralArithmetic.PrimeCoordinates
lake build DkMath.NumberTheory.StructuralArithmetic.KUSObservation
lake build DkMath.NumberTheory.StructuralArithmetic
git diff --check
```

The new source contains no `sorry`, `admit`, `axiom`, or `unsafe`.  Axiom
audits of the rpow reconstruction, `y = 3` boundary, dynamic support theorem,
and `y = 30` reconstruction report only inherited standard Lean/Mathlib
dependencies (`propext`, `Classical.choice`, and `Quot.sound`).  The existing
transitive `ZsigmondyCyclotomicResearch.lean:147` `sorry` warning is unchanged.

The next bounded direction may use this scalar in a more specific DHNT/Cosmic
Formula application, but global real prime-factorization reconstruction remains
outside Phase I.
