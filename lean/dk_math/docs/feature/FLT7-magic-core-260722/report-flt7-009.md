# FLT7-009 implementation report

## Outcome

Outcome A. Primitive coordinate coprimality, exceptional axis support,
`sevenAxis` primality, both route conjugate-coprimality results, and exact
element-level seventh-power normal forms are complete. The checkpoint stops
before coordinate expansion or descent.

## Files changed

- `DkMath/FLT/Seven/PrimitiveCoordinateCoprime.lean`
- `DkMath/FLT/Seven/QuadraticConjugateCoprime.lean`
- `DkMath/FLT/Seven/QuadraticSeventhPowerNormalForm.lean`
- `DkMath/FLT/Seven.lean`
- `DkMathTest/FLT/SevenPrimitiveCoordinateCoprime.lean`
- `DkMathTest/FLT/SevenQuadraticSeventhPowerNormalForm.lean`
- `docs/feature/FLT7-magic-core-260722/report-flt7-009.md`

## Primitive coordinate surface

- `prime_dvd_both_cyclotomicSeven_coordinates`
- `cyclotomicSeven_coordinates_isCoprime`
- `counterexample_cyclotomicSeven_coordinates_isCoprime`

For a prime `q`, both cubic coordinates are moved to `ZMod q`. The second is
`-z*y*(z+y)`, giving the branches `z=0`, `y=0`, or `z+y=0`. In every branch
the first coordinate forces the remaining endpoint to vanish. Thus a common
prime divisor divides both natural endpoints, contradicting primitive
coprimality. Applying this to a prime factor of the integer gcd yields the
stable integer Bézout certificate.

## Exceptional-divisor support

- `sub_conj_eq_snd_mul_sevenAxis`
- `sevenAxis_mul_sub_tau_mul_sub_conj`
- `common_divisor_dvd_sevenAxis_of_coordinate_coprime`
- `common_divisor_cyclotomic_conj_dvd_sevenAxis`

The first identity shows a common divisor divides `snd*wAxis`; the companion
identity gives divisibility of `fst*wAxis`. Bézout coefficients for `fst,snd`
combine these two facts and prove that every common divisor of a primitive
coordinate and its conjugate divides `sevenAxis`.

## Axis primality

- `irreducible_sevenAxis`
- `prime_sevenAxis`
- `isUnit_of_dvd_sevenAxis_of_dvd_terminal`

The norm of `sevenAxis` is the integer prime `7`. In a factorization, positive
nonzero factor norms multiply to `7`, so one has norm one and is a unit. The
Euclidean infrastructure converts irreducibility to primality. A divisor of
the axis that also divides a terminal element must be a unit, since the
associated-axis alternative contradicts terminality.

## Away route

- `cyclotomicSeven_gcd_conj_isUnit_of_not_seven_dvd_gap`
- `exists_cyclotomicSeven_eq_seventh_power_of_away`

The coordinate support theorem forces the conjugate gcd to divide the axis.
A nonunit gcd would make the axis divide the coordinate, contradicting the
existing axis/gap criterion. The natural away split supplies `GN=v^7`, hence
`C*conj C=v^7`; exact coprime factor extraction gives `C=gamma^7`.

## Ramified route and summit

- `SevenQuadraticResidualPacket.gcd_residual_conj_isUnit`
- `SevenQuadraticResidualPacket.exists_residualCore_eq_seventh_power`
- `SevenQuadraticSeventhPowerPacket`
- `nonempty_sevenQuadraticSeventhPowerPacket_of_residual`
- `sevenQuadraticSeventhPowerPacket_of_residual`
- `sevenQuadraticSeventhPowerPacket_of_counterexample`
- `QuadraticCounterexampleRoute`
- `quadraticCounterexampleRoute_of_pack`

Multiplying a common residual/conjugate divisor by the peeled axis places it
under the full primitive coordinate support. Terminality removes the only
exceptional axis factor, so the residual gcd is a unit. The exact norm identity
then promotes `norm residual=b^7` to `residual=gamma^7` using FLT7-008.

The final route classification is exactly

```text
Away:     cyclotomic coordinate = gamma^7
Ramified: cyclotomic coordinate = sevenAxis * gamma^7.
```

## Scope preserved

No coordinate descent, FLT7 contradiction/no-solution theorem, general-prime
cyclotomic theorem, ideal/class-number theory, new unit sector, or FLT3/FLT5
change was added.

## Verification

The following checks passed:

- `lake build DkMath.FLT.Seven.PrimitiveCoordinateCoprime`
- `lake build DkMath.FLT.Seven.QuadraticConjugateCoprime`
- `lake build DkMath.FLT.Seven.QuadraticSeventhPowerNormalForm`
- `lake build DkMath.FLT.Seven`
- `lake env lean DkMathTest/FLT/SevenPrimitiveCoordinateCoprime.lean`
- `lake env lean DkMathTest/FLT/SevenQuadraticSeventhPowerNormalForm.lean`
- `lake build DkMath.FLT`
- forbidden-token scan over the new modules and focused tests
- `git diff --check`

The tests use abstract inputs only and cover both final route constructors.
Every audited theorem reports exactly
`[propext, Classical.choice, Quot.sound]`; there are no project-specific axioms
and no `native_decide`, `admit`, or `sorry` in this checkpoint.

## Recommended FLT7-010 boundary

Expand both element-level normal forms through explicit coordinates of
`(u+v*tau)^7` and isolate the resulting finite sign/unit sector. Since all
units are already absorbed, the next obstruction must come from those
coordinate equations or a proved strict transformation, not a hidden unit
class. Do not claim descent until its decreasing measure is explicit.
