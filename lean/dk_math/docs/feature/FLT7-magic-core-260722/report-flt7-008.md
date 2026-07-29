# FLT7-008 implementation report

## Outcome

Outcome A. `TraceOneInt (-2)` now has a direct domain proof, explicit
norm-Euclidean division, complete unit classification, and exact coprime
seventh-power factor extraction. This checkpoint does not apply the extraction
theorem to the FLT7 residual packet.

## Files changed

- `DkMath/FLT/Seven/QuadraticEuclidean.lean`
- `DkMath/FLT/Seven/QuadraticUnits.lean`
- `DkMath/FLT/Seven/QuadraticCoprimeFactor.lean`
- `DkMath/FLT/Seven.lean`
- `DkMathTest/FLT/SevenQuadraticEuclidean.lean`
- `DkMathTest/FLT/SevenQuadraticCoprimeFactor.lean`
- `docs/feature/FLT7-magic-core-260722/report-flt7-008.md`

## Domain and instance surface

- `traceOneNegTwo_eq_zero_or_eq_zero_of_mul_eq_zero`
- `traceOneNegTwoNoZeroDivisors`
- `traceOneNegTwoNontrivial`
- `traceOneNegTwoIsDomain`
- `traceOneNegTwoEuclideanDomain`
- `traceOneNegTwoGCDMonoid`

Norm multiplicativity turns `x*y=0` into `norm x * norm y=0`. Integer
zero-product elimination and the existing zero fiber of the positive norm then
give `x=0 ∨ y=0`; no generic quadratic-domain claim is introduced.

## Skew nearest-lattice division

The rational layer exposes `SevenRat`, `sevenRatNorm`,
`sevenQuotientNumerator`, `sevenQuotientCoords`, `sevenRoundedSnd`,
`sevenRoundedFst`, `sevenQuotient`, `sevenRemainder`, and
`sevenEuclideanSize`.

Independent coordinate rounding does not control the cross term efficiently
for discriminant `-7`. Instead, with quotient coordinates `(A,B)`, the
algorithm first takes `n=round B`, puts `v=B-n`, and then takes
`m=round(A+v/2)`. Thus both `|v|` and `|u+v/2|`, where `u=A-m`, are at most
`1/2`.

The completed square

```text
u^2+uv+2v^2 = (u+v/2)^2 + (7/4)v^2
```

therefore gives the exact rational bound `11/16<1`. The rational remainder
norm identity transfers this contraction to strict decrease of
`natAbs(norm remainder)`. Together with quotient/remainder reconstruction and
multiplicativity of the size, this supplies the EuclideanDomain instance.

## Unit classification

- `isUnit_iff_norm_eq_one`
- `isUnit_iff_eq_one_or_neg_one`
- `exists_seventh_power_eq_of_isUnit`

A unit and its inverse have positive integral norms whose product is one, so
the unit norm is one. The existing norm-one shell is exactly `±1`. Since seven
is odd, both signs are themselves seventh powers; consequently every unit can
be absorbed into a seventh-power base.

## Coprime factor extraction

- `associated_seventh_power_of_coprime_mul_eq_pow`
- `exists_eq_seventh_power_of_coprime_mul_eq_pow`
- `seventh_power_factor_split_traceOneNegTwo`

The Euclidean gcd structure feeds Mathlib's associated-power extraction.
Expanding the association exposes a unit multiplier, and the odd-power unit
theorem absorbs it. Hence each coprime factor of a seventh power is exactly a
seventh power, not only associated to one.

## Scope preserved

No residual-packet application, conjugate coprimality, descent, FLT7
contradiction, ideal/class-number theory, generic quadratic Euclidean instance,
or FLT3/FLT5 change was added.

## Verification

The following checks passed:

- `lake build DkMath.FLT.Seven.QuadraticEuclidean`
- `lake build DkMath.FLT.Seven.QuadraticUnits`
- `lake build DkMath.FLT.Seven.QuadraticCoprimeFactor`
- `lake build DkMath.FLT.Seven`
- `lake env lean DkMathTest/FLT/SevenQuadraticEuclidean.lean`
- `lake env lean DkMathTest/FLT/SevenQuadraticCoprimeFactor.lean`
- `lake build DkMath.FLT`
- forbidden-token scan over the new modules and focused tests
- `git diff --check`

The tests cover symbolic rounding bounds, strict decrease for two explicit
nonzero divisors, Euclidean gcd availability, unit/nonunit examples, both unit
seventh powers, and abstract factor splitting. Every audited theorem reports
exactly `[propext, Classical.choice, Quot.sound]`; there are no project-specific
axioms and no `native_decide`, `admit`, or `sorry` in this checkpoint.

## Recommended FLT7-009 boundary

Prove coprimality of the terminal quadratic residual and its conjugate, or
isolate the exact exceptional-divisor support. Only after that bridge is
complete should `SevenQuadraticResidualPacket` be promoted from a
seventh-power norm statement to an element-level seventh-power normal form.
