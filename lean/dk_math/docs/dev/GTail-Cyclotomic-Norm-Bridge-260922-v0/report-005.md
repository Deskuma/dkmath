# GCNB-008 implementation report

## Result

Outcome A: the p = 3, 5, 7 dedicated fixed-prime norm carriers are now
calibrated against the generic cyclotomic ideal absolute norm, and the
generic TraceOne packet norm is transported to each dedicated scalar.

The production module is:

```text
DkMath/FLT/Prime/PrimeCyclotomicCalibration.lean
```

It is exported through `DkMath.FLT.Prime`.

## Dedicated calibrations

The module provides:

```lean
cyclotomicIdeal_absNorm_eq_traceOneNorm_three
cyclotomicIdeal_absNorm_eq_traceOneNorm_five
cyclotomicIdeal_absNorm_eq_goldenNorm_squareLink
cyclotomicIdeal_absNorm_eq_traceOneNorm_seven
```

The p = 3 theorem reuses
`DkMath.FLT.GN_three_sub_eq_traceOneNorm_negOne` at endpoint `g + u` and
base `u`. The p = 5 theorems reuse
`GN5_eq_generic_GN` and the existing square-link bridges. The p = 7 theorem
reuses `DkMath.FLT.Seven.GN_seven_sub_eq_traceOneNorm_negTwo`.

All three proofs use the generic ideal norm theorem and the arithmetic identity
`(g + u) - u = g`; no positivity hypothesis on `g` or `u` is introduced.

## Generic packet calibration

The following scalar-only packet theorems are exported:

```lean
coord_norm_eq_traceOneNorm_three
coord_norm_eq_traceOneNorm_five
coord_norm_eq_traceOneNorm_seven
```

Each is proved by transitivity through
`TraceOneScalar.coord_norm_eq_cyclotomicIdeal_absNorm`. No equality of
coordinates, elements, ideals, or rings is asserted.

The p = 3 signed carrier alignment is checked through the existing
`traceOneInt_signedPrimeParameter_three_type` theorem. The tests also record
`signedPrimeParameter 3 = -1`, `signedPrimeParameter 5 = 1`, and
`signedPrimeParameter 7 = -2`.

## Regression coverage

`DkMathTest/FLT/Prime/PrimeCyclotomicCalibration.lean` checks:

- p = 3 ideal norm against `TraceOneInt (-1)`, including `(g,u)=(0,0)`;
- p = 5 ideal norm against the square-link `TraceOneInt 1` norm and `GoldenNorm`;
- p = 7 ideal norm against `cyclotomicSevenToTraceOne`;
- generic packet norm calibration at p = 3, 5, and 7;
- zero-boundary cases for p = 3, 5, and 7;
- all new public theorem axiom sets with `#print axioms`.

No FLT3/FLT5 endpoint proof was refactored, and no FLT counterexample or
arbitrary-prime FLT conclusion is asserted.

## Firewall

This checkpoint transports only checked scalar norm values. It does not claim
generic packet coordinate-element equality with Eisenstein, Golden, or explicit
p = 7 cubic coordinates; it does not identify cyclotomic ideals with TraceOne
ideals; and it does not infer prime-ideal multiplicities, principalization,
class-group consequences, or FLT7 re-entry.

## Validation

The required focused and regression builds completed successfully:

```text
lake build DkMath.FLT.Prime.PrimeCyclotomicCalibration
lake build DkMathTest.FLT.Prime.PrimeCyclotomicCalibration
lake build DkMath.FLT.Prime
lake build DkMath.FLT.Three
lake build DkMath.FLT.Five
lake build DkMath.FLT.Seven.QuadraticBridge
lake build DkMath
git diff --check
```

The new production and test source contains no `sorry`, `admit`, `sorryAx`,
`unsafe`, or new `axiom`. Existing warnings in
`DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147` and
`DkMath/FLT/Kummer/CyclotomicPrincipalization.lean:5389` remain outside this
checkpoint.
