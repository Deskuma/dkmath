# CPG-V1-001 — CF2D return and congruence bridge

Date: 2026-09-12  
Status: complete

## Implemented API

Added the thin production module
[Return.lean](../../../DkMath/NumberTheory/PrimeGauge/Return.lean):

```lean
DkMath.NumberTheory.PrimeGauge.regularKernel_pow_eq_one_iff_dvd
DkMath.NumberTheory.PrimeGauge.regularKernel_pow_eq_pow_iff_modEq
```

The first theorem composes the existing
`DkMath.CosmicFormula.Rotation.CF2D.orderOf_regularKernel` with Mathlib's
`orderOf_dvd_iff_pow_eq_one`. The second composes the same exact-order theorem
with Mathlib's `pow_eq_pow_iff_modEq`. No new cyclic-gauge structure or
prime-order claim was added.

Added the focused regression file
[PrimeGaugeReturn.lean](../../../DkMathTest/NumberTheory/PrimeGaugeReturn.lean).
It checks return at periods `2`, `3`, `5`, and `6`, return at multiples and
zero, non-return at nonmultiples, and phase equality/non-equality modulo `5`.

## Scope boundary

- No Goldbach definitions or residue theorems were changed.
- No Projection or continuum API was added.
- No Prime Gauge aggregator was added; the new module is directly importable,
  keeping this checkpoint's import surface narrow.
- The result is a finite phase/divisibility observer only. It does not imply
  primality of `k`, prime existence, Goldbach, or any universal escape result.

## Validation

Executed from `lean/dk_math`:

```bash
lake build DkMath.NumberTheory.PrimeGauge.Return \
  DkMathTest.NumberTheory.PrimeGaugeReturn
```

Result: exit 0, `Build completed successfully (8694 jobs)`.

Additional checks on the fresh build log:

- independent `warning:` scan: no matches;
- forbidden-construct scan of the two new Lean files: no matches for
  `sorry`, `admit`, user `axiom`, `unsafe`, or `native_decide`;
- `#print axioms` for both new theorems: only `propext`, `Classical.choice`,
  and `Quot.sound`.

The shell profile emitted an environment permission warning before Lake; the
Lean build itself completed without errors or warnings.

## Roadmap transition

`CPG-V1-001` is complete. The next checkpoint is `CPG-V1-002`, which must
bridge the existing Goldbach `ZMod` left/right residue observer to the CF2D
phase vocabulary while retaining `u ≤ n` and raw/proper obstruction
boundaries.

