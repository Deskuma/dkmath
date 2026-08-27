# DHNT radial scaling / rebase distinction implementation report

## Scope and baseline

This report closes the Phase H acceptance set in
`CODEX-DHNT-RADIAL-SCALING-REBASE-DIRECTIVE-260820.md`.  The implementation
started from checkpoint `1278d3c555044d3f14a5c069394e00c5798b0956` and is
confined to the StructuralArithmetic module, aggregate, README, and this
report.  KUS and completed FLT5 modules were not modified.

## Representation and theorem list

`RadialScaling.lean` specializes to real-valued vectors with a fixed index
type:

- `radialScaleCoordinates k v i = k * v i`;
- `radialScaleCoordinates_one`, `radialScaleCoordinates_zero`, and
  `radialScaleCoordinates_mul` provide identity, collapse, and composition;
- `radialScaleCoordinates_eq_zero_iff` proves coordinate zero-pattern
  preservation for `k ≠ 0`;
- `support_radialScaleCoordinates` lifts this to `Function.support`;
- `radialScale_ne_of_source_nonzero_target_zero` states that a nonzero radial
  scale cannot equal a target that erases a nonzero source coordinate.

The existing `primeExponentCoordinates` source is reused through
`realPrimeExponentCoordinates` and `radialScalePrimeCoordinates`, with the
specialized zero-pattern theorem
`radialScalePrimeCoordinates_eq_zero_iff`.  These are real-valued images of
natural valuation coordinates, not prime factorizations in `ℝ`.

The module documentation records the semantic boundary: KUS `ScaleSpec` is a
typed support/unit/blueprint transport or rebase operation, while radial
scaling is fixed-index scalar multiplication.  PowerGauge projection remains
natural exponent reduction modulo a period.  No `Real.log`, `Real.rpow`,
analytic reconstruction, quotient hierarchy, or project-specific axiom was
introduced.

## Verification

Focused builds completed successfully:

```text
lake build DkMath.NumberTheory.StructuralArithmetic.RadialScaling
lake build DkMath.NumberTheory.StructuralArithmetic.PrimeCoordinates
lake build DkMath.NumberTheory.StructuralArithmetic.KUSObservation
lake build DkMath.NumberTheory.StructuralArithmetic
git diff --check
```

The new source contains no `sorry`, `admit`, `axiom`, or `unsafe`.  The
load-bearing support and prime-coordinate theorems use only the standard
axiom dependencies reported by Lean (`propext`; the prime-coordinate import
also inherits the existing development dependencies).  The pre-existing
transitive `ZsigmondyCyclotomicResearch.lean:147` `sorry` warning remains
unchanged.

The next phase may consider a bounded analytic DHNT/Cosmic Formula scaling
example, but global real prime-factorization reconstruction is intentionally
outside this checkpoint.
