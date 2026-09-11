# FLT prime-generalization Phase 6 — Gaussian-period factorization frontier

## Scope and outcome

This report implements the bounded contract in `instruction-006.md`.  The
phase adds neutral conjugate-factor algebra, a kernel-checked signed-prime
discriminant probe, and the QR/QNR finite partition and product-recombination
layer.  It does not change the FLT3, FLT5, or FLT7 endpoints and does not
claim a general FLT theorem.

The highest reached classification is:

```text
PGEN-GAUSS-QR-PARTITION
```

The QR/QNR finite combinatorics is formalized, including the expected
cardinalities and a weak abstract product identity.  The first missing
theorem is the identification of that product with a primitive-root
cyclotomic shell for an arbitrary odd prime.

## Part A — neutral conjugate-factor algebra

Added:

```text
DkMath/NumberTheory/QuadraticConjugateFactor.lean
```

The production API is independent of cyclotomic fields:

```text
add_sq_sub_four_mul_eq_sub_sq
four_mul_product_eq_sum_sq_sub_discriminant_mul
```

For a commutative ring it proves

```text
(U + V)^2 - 4 * (U * V) = (U - V)^2
```

and the division-free rearrangement from `R = U + V`, `C = U * V`, and
`(U - V)^2 = D * S^2` to
`4 * C = R^2 - T * S^2` when `T = D`.

The test module connects this identity to the Phase-5 adapter through:

```text
traceOne_norm_from_conjugate_form
```

Once `R = 2*A + S` and the Gauss form are supplied, it recovers
`norm (⟨A,S⟩ : TraceOneInt s) = C` using
`norm_eq_of_gauss_coordinates`.

## Part B — bounded signed-prime discriminant audit

The test-side representation is:

```text
signedPrimeDiscriminant p :=
  if p % 4 = 1 then (p : ℤ) else -(p : ℤ)
signedPrimeParameter p := (signedPrimeDiscriminant p - 1) / 4
```

The following are kernel-checked:

```text
signedPrimeDiscriminant_eq_or_neg
signedPrimeDiscriminant_natAbs
signedPrimeDiscriminant_mod_four
discr_signedPrimeParameter
```

The modulo-four theorem assumes `p.Prime` and `p ≠ 2`; it uses the pinned
prime oddness API and proves `D % 4 = 1`.  The parameter theorem then proves
`discr (signedPrimeParameter p) = D` using integer Euclidean division.

No production canonical wrapper for the signed Legendre-symbol formula is
introduced.  The pinned Mathlib audit found the quadratic-character and
Legendre APIs, but no single theorem that directly supplies the required
integral TraceOne parameter and all sign/division obligations.

The bounded samples are retained and checked for `p = 3, 5, 7, 11, 13`.
In particular:

```text
p = 11: D = -11, s = -3
p = 13: D =  13, s =  3
```

## Part C1 — QR/QNR finite partition

Added to:

```text
DkMathTest/FLT/Prime/GaussianPeriodFactorizationProbe.lean
```

The probe defines nonzero residue classes in `ZMod p` and filters them by
`IsSquare`:

```text
nonzeroResidues
qrFinset
qnrFinset
```

Using the pinned Mathlib declarations
`quadraticChar_dichotomy`,
`quadraticChar_one_iff_isSquare`,
`quadraticChar_neg_one_iff_not_isSquare`, and
`quadraticChar_sum_zero`, it proves:

```text
qr_qnr_disjoint
qr_qnr_union
qr_card_add_qnr_card
qr_card_eq_half
qnr_card_eq_half
```

For an odd prime, both cards are `(p - 1) / 2` and their disjoint union is
the nonzero classes.

## Part C2 — weak product recombination

For any commutative monoid `R` and any function `f : ZMod p → R`, the probe
proves:

```text
qr_product_mul_qnr_product
```

This is the finite identity

```text
(∏ a ∈ QR, f a) * (∏ a ∈ QNR, f a)
  = ∏ a ∈ (ZMod p \ {0}), f a
```

It is deliberately the weakest C2 statement.  It does not pretend that `f`
is already an evaluated primitive-root factor.

## Part C3/C4 — exact frontier

The pinned APIs audited include:

- `ZMod.euler_criterion`, `ZMod.ringChar_zmod_n`, and the Legendre/character
  declarations in `Mathlib.NumberTheory.LegendreSymbol.Basic`;
- `quadraticChar_dichotomy`,
  `quadraticChar_one_iff_isSquare`,
  `quadraticChar_neg_one_iff_not_isSquare`,
  `quadraticChar_sum_zero`, and `quadraticChar_card_sqrts`;
- `gaussSum`, `gaussSum_sq`, and the character-cardinality lemmas in
  `Mathlib.NumberTheory.GaussSum` and
  `Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum`;
- `Polynomial.cyclotomic_prime`,
  `Polynomial.cyclotomic_prime_mul_X_sub_one`, and
  `Polynomial.cyclotomic_prime_pow_eq_geom_sum`;
- the project shell declarations
  `GTailCyclotomicShell`,
  `GTailCyclotomicHomEval_prime_eq_shell`, and
  `GTail_one_eq_cyclotomicHomEval_of_prime`.

The missing C3 bridge is a typed construction placing the QR/QNR factors in a
common ring with a primitive `p`-th root and identifying their full product
with the evaluated homogeneous prime cyclotomic shell.  The missing C4
bridge is the corresponding Galois/conjugation action and coefficient
descent.  Consequently no integral `R_p,S_p`, square-root normalization, or
arbitrary-prime Gauss form is claimed.

The exact first missing theorem is therefore:

```text
For every odd prime p, identify the QR/QNR product over primitive-root
factors with GTailCyclotomicShell p (z-y) y in a specified coefficient ring.
```

This is why the classification remains `PGEN-GAUSS-QR-PARTITION`, rather than
`PGEN-GAUSS-FACTOR-GREEN` or a conjugation/integrality classification.

## Part E — finite compatibility

Added:

```text
DkMathTest/FLT/Prime/GaussianPeriodFactorizationCompatibility.lean
```

The existing exact p=11 and p=13 polynomial regressions remain available:

```text
norm11_direct
norm13_direct
norm11
norm13
```

The compatibility module checks that the new work leaves both norm paths
unchanged.  The existing p=3, p=5, and p=7 TraceOne compatibility module is
also retained and was rebuilt.

## Part F — FLT relevance boundary

The three layers remain distinct:

```text
1. generic odd-prime GTail / PrimeAdicPowerSplit          [GREEN]
2. generic prime-discriminant TraceOne axis / Gauss form [GREEN]
3. arbitrary-prime Gaussian-period integral coordinates  [this phase: OPEN]
```

Even a future GREEN result for layer 3 would only generalize the quadratic
cyclotomic front-end.  It would not by itself prove general FLT; unit-class,
ideal-factorization, class-group, descent, and contradiction layers would
still require separate audits.

## Verification

The focused builds passed:

```text
lake build DkMath.NumberTheory.QuadraticConjugateFactor
lake build DkMath.NumberTheory.TraceOneDiscriminantAxis
lake build DkMath.FLT.Prime.AdicPowerSplit
lake build DkMathTest.FLT.Prime.GaussianPeriodFactorizationProbe
lake build DkMathTest.FLT.Prime.GaussianPeriodFactorizationCompatibility
lake build DkMathTest.FLT.Prime.GaussianPeriodFactorizationAxiomAudit
lake build DkMathTest.FLT.Prime.QuadraticCyclotomicBridgeProbe
lake build DkMathTest.FLT.Prime.TraceOneDiscriminantAxisCompatibility
lake build DkMathTest.FLT.Prime.TraceOneDiscriminantAxisAxiomAudit
lake build DkMath.FLT.Seven
```

The focused production axiom audit reports only Lean kernel support
(`propext` and `Quot.sound`) for the two new neutral declarations.  The test
probe uses `Classical.choice` for finite-set decidability, but no
`sorryAx` appears.  The changed files contain no `sorry` or explicit `axiom`
construct.

No FLT3, FLT5, FLT7, general FLT, or arbitrary-prime integral-coordinate
theorem is claimed by this phase.
