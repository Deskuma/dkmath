# FLT prime-generalization Phase 12 — quadratic Gauss normalization and integral `S_p`

## Scope and outcome

This report records the bounded implementation requested by
`instruction-012.md`. The Phase-11 integral cyclotomic descent is extended
through the quadratic Gauss square root, common character eigenspace, rational
coefficient descent, and integral `S_p` extraction.

The resulting classification is:

```text
PGEN-GAUSS-SQUARE-NORMALIZATION-GREEN
```

The implementation stops at the mapped discriminant-square normalization. It
does not add `R_p - S_p = 2 * A_p`, arbitrary-prime TraceOne coordinates, a
unit/class-group descent contradiction, or a general FLT theorem.

## A. Production signed discriminant API

The new neutral module is:

```text
DkMath/NumberTheory/PrimeQuadraticDiscriminant.lean
```

It provides:

```text
signedPrimeDiscriminant
signedPrimeParameter
signedPrimeDiscriminant_eq_or_neg
signedPrimeDiscriminant_natAbs
signedPrimeDiscriminant_mod_four
discr_signedPrimeParameter
```

The sign is represented in `ℤ` by the modulo-four branch, and the production
theorems establish the signed-prime alternatives, absolute value, modulo-four
condition, and `1 + 4 * s_p = D_p` through the existing `discr` API.

## B. Gauss element and Galois character law

The main production module is:

```text
DkMath/NumberTheory/CyclotomicQRGaussNormalization.lean
```

The selected pinned Mathlib route uses:

```text
gaussSum_sq
AddChar.zmodChar
AddChar.zmodChar_primitive_of_primitive_root
AddChar.mulShift_apply
```

The project wrapper `quadraticGauss` is defined in an arbitrary cyclotomic
extension over `ℚ`, with:

```text
quadraticGauss_sq
quadraticGauss_ne_zero
```

The square theorem has the normalized form:

```lean
quadraticGauss ζ hζ ^ 2 =
  algebraMap ℤ L (signedPrimeDiscriminant p)
```

The Galois action is packaged by:

```text
map_quadraticGauss_of_power
map_quadraticGauss_of_cyclotomicAut
```

and uses the Phase-9 `cyclotomicAut_power_spec` exponent. The resulting
character factor is `+1` on squares and `-1` on nonsquares through the pinned
quadratic-character dichotomy.

## C. Rational eigenspace coefficients

For every monomial index `d`, the quotient of the `Dpoly` coefficient by the
nonzero Gauss element is shown fixed by every `ℚ`-automorphism. Existing
fixed-field descent then gives:

```text
coeff_Dpoly_eq_gauss_mul_rat
```

with an existential rational coefficient and no exported chosen witness.

## D. Squarefree rational denominator lemma

The reusable arithmetic module is:

```text
DkMath/NumberTheory/RationalSquarefreePrime.lean
```

It provides:

```text
rat_eq_int_of_prime_mul_sq
rat_eq_int_of_signedPrime_mul_sq
```

The proof uses `Rat.num`, `Rat.den`, `Rat.mul_den`, `Rat.mul_self_num`,
`Rat.mul_self_den`, and the reduced numerator/denominator coprimality to
derive `den(q)^2 ∣ p`. Primality forces the denominator to be one; the signed
case is reduced to the positive case by negating the integral witness.

## E. Integral `S_p` extraction

The Phase-11 production API is extended with:

```text
Dpoly_integral
coeff_Dpoly_isIntegral_int
```

This supplies the coefficient integrality needed for the square argument. For
each coefficient, `quadraticGauss_sq`, the rational-integral bridge, and the
squarefree denominator lemma give an integer coefficient multiplying the
Gauss element.

The resulting production theorem is:

```text
exists_Dpoly_over_gauss_int
```

It constructs an existential `SZ : MvPolynomial (Fin 2) ℤ` satisfying the
mapped factorization with `quadraticGauss ζ hζ`. The witness is built through
the coefficient-range API and is not identified with any explicit p=11 or
p=13 witness.

## F. Discriminant-square normalization

The final production endpoint is:

```text
exists_Dpoly_square_normalization
```

It proves, for odd prime `p` in the selected cyclotomic extension, an
existential `SZ` with:

```lean
Dpoly (p := p) ζ ^ 2 =
  MvPolynomial.C (algebraMap ℤ L (signedPrimeDiscriminant p)) *
    (MvPolynomial.map (algebraMap ℤ L) SZ) ^ 2
```

The proof squares the mapped Gauss factorization and rewrites the Gauss square
using `quadraticGauss_sq`.

## G. Finite compatibility and audits

The focused test modules are:

```text
DkMathTest/FLT/Prime/CyclotomicQRGaussNormalizationProbe.lean
DkMathTest/FLT/Prime/CyclotomicQRGaussNormalizationCompatibility.lean
DkMathTest/FLT/Prime/CyclotomicQRGaussNormalizationAxiomAudit.lean
```

The probe checks the production normalization for:

```text
p = 3, 5, 7, 11, 13
```

The compatibility module checks `D_11 = -11`, `D_13 = 13`, the corresponding
trace-one discriminants, and the existing explicit `gauss_form11` and
`gauss_form13` square identities. It keeps the new existential witnesses
separate from `B11` and `B13`.

The axiom audit covers the Gauss square, nonzero, Galois action, rational
coefficient, rational squarefree, integer coefficient, and final normalization
theorems. The reported dependencies are the inherited kernel dependencies
`propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`, new `sorry`, or
explicit `axiom` occurs in the Phase-12 sources.

## Verification

The final focused build passed for the production discriminant, Phase-9/10/11
chain, rational squarefree module, Gauss normalization module, all three new
test modules, and `DkMath.FLT.Seven`.

A fresh build-log warning scan produced no warnings after filtering the
standard `declaration uses \`sorry\`` pattern. `git diff --check` also passed.

## Next boundary

```text
R_p - S_p = 2 * A_p parity / arbitrary-prime TraceOne bridge
```
