# FLT7-001 implementation report

## Outcome

Outcome A.  The required magic core, positive-definite norm, seventh
cyclotomic/GN bridge, coordinate zero fiber, tests, and documentation are all
implemented.  The optional positive-natural lower bound is also complete.

## Files changed

- `DkMath/NumberTheory/TraceOneQuadratic.lean`
- `DkMath/FLT/Seven/QuadraticBridge.lean`
- `DkMath/FLT/Seven.lean`
- `DkMath/FLT.lean`
- `DkMathTest/FLT/SevenQuadraticBridge.lean`
- `docs/feature/FLT7-magic-core-260722/README.md`
- `docs/feature/FLT7-magic-core-260722/report-flt7-001.md`

## Exact implementation surface

Definitions:

- `sevenAxis`
- `cyclotomicSeven`
- `cyclotomicSevenFst`
- `cyclotomicSevenSnd`
- `cyclotomicSevenToTraceOne`

Axis and norm theorems:

- `sevenAxis_eq`, `sevenAxis_fst`, `sevenAxis_snd`
- `sevenAxis_sq`, `conj_sevenAxis`, `sevenAxis_norm`
- `traceOneNorm_neg_two`
- `four_mul_traceOneNorm_negTwo_eq_sum_sq`
- `traceOneNorm_negTwo_eq_zero_iff`, `norm_eq_zero_iff_of_negTwo`
- `one_le_traceOneNorm_negTwo_of_ne_zero`
- `traceOneNorm_negTwo_eq_one_iff`, `norm_eq_one_iff_of_negTwo`

Cyclotomic bridge theorems:

- `cyclotomicSeven_eq_traceOneNorm_negTwo`
- `seventh_pow_sub_pow_eq_sub_mul_cyclotomicSeven`
- `GN_seven_sub_eq_traceOneNorm_negTwo`
- `cyclotomicSeven_coordinates_eq_zero_iff`
- `cyclotomicSeven_eq_zero_iff`
- `seven_le_cyclotomicSeven_nat`

## Mathematical results

The central scale axis has coordinates `(-1,2)`.  The theorem
`sevenAxis_sq` states equality in the ring `TraceOneInt (-2)` between its
square and the embedded integer `-7`; it is not a claim that the axis is a
unit.  Conjugation negates it and its norm is exactly `7`.

The specialized norm is `a^2+a*b+2*b^2`, with
`4*N=(2*a+b)^2+7*b^2`.  It is zero exactly at `(0,0)`.  Every nonzero
structured element has integer norm at least `1`, and norm `1` occurs exactly
at coordinate pairs `(1,0)` and `(-1,0)`, equivalently at the ring elements
`1` and `-1`.

For endpoints `(z,y)`, the cubic pair

```text
(z^3+z^2*y-y^3, -z^2*y-z*y^2)
```

has `s=-2` norm equal to the homogeneous seventh cyclotomic polynomial.  The
coordinate pair and the norm vanish exactly when both endpoints vanish.

The exact GN substitution is `g=a-b`, base `b`, endpoint
`g+b=(a-b)+b=a`, under `b≤a`.  Thus `GN 7 (a-b) b`, after casting to integers,
equals the norm of `cyclotomicSevenToTraceOne a b`.

The optional natural result is complete: for positive `z,y`, the sum of the
seven monomials is at least `7`.  This is distinct from the full integral
nonzero norm floor `1`.

## Verification and axiom audit

The required focused builds, Lean test file, forbidden-token scan, and
`git diff --check` are run at the close of this checkpoint.  The exact
`#print axioms` sets are:

- `traceOne_tau_sq`: `propext`, `Classical.choice`, `Quot.sound`
- `traceOne_norm_mul`: `propext`, `Quot.sound`
- `sevenAxis_sq`: `propext`, `Classical.choice`, `Quot.sound`
- `sevenAxis_norm`: `propext`, `Quot.sound`
- `traceOneNorm_negTwo_eq_zero_iff`: `propext`, `Classical.choice`, `Quot.sound`
- `one_le_traceOneNorm_negTwo_of_ne_zero`: `propext`, `Classical.choice`, `Quot.sound`
- `traceOneNorm_negTwo_eq_one_iff`: `propext`, `Classical.choice`, `Quot.sound`
- `cyclotomicSeven_eq_traceOneNorm_negTwo`: `propext`, `Classical.choice`, `Quot.sound`
- `cyclotomicSeven_eq_zero_iff`: `propext`, `Classical.choice`, `Quot.sound`

These are standard Lean axioms; no `sorryAx` or DkMath-defined axiom appears.
No active `native_decide`, `admit`, or `sorry` is used in the new FLT7
implementation or test.

## Non-goals preserved

No FLT7 theorem, descent, counterexample packet, unit-sector theory,
Euclidean/PID/UFD/class-number-one structure, prime classification, general
odd-prime generalization, or standalone proof artifact was added.  FLT3 and
FLT5 statements were left unchanged; FLT7 imports only the neutral core and
the generic GN layer.

## Recommended next checkpoint

FLT7-002: seven-axis divisibility and the relation between kappa-depth and
7-adic norm depth.
