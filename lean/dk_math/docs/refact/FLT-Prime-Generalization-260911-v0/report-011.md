# FLT prime-generalization Phase 11 — integral coefficient descent

## Scope and outcome

This report records the bounded implementation requested by
`instruction-011.md`. Phase 10 whole-polynomial descent over `ℚ` is refined
to whole-polynomial descent over `ℤ` for `Rpoly ζ` and `Dpoly ζ ^ 2` in an
arbitrary prime cyclotomic extension.

The resulting classification is:

```text
PGEN-GAUSS-ZDESCENT-GREEN
```

The work stops before integral Gaussian-coordinate extraction. It does not
construct `S_p`, identify `Dpoly` with `√D_p * S_p`, alter FLT3/FLT5/FLT7
endpoints, or claim an FLT contradiction.

## A. Pinned API audit and selected route

The audit module is:

```text
DkMathTest/FLT/Prime/CyclotomicQRIntegralDescentAxiomAudit.lean
```

The pinned integrality APIs confirmed and used are:

```text
IsPrimitiveRoot.isIntegral
MvPolynomial.isIntegral_iff_isIntegral_coeff
IsIntegral.add
IsIntegral.sub
IsIntegral.mul
IsIntegral.pow
isIntegral_algebraMap_iff
IsIntegrallyClosed.isIntegral_iff
MvPolynomial.mem_range_map_iff_coeffs_subset
```

The pinned ring-of-integers APIs also audited are:

```text
IsIntegralClosure.isIntegral_iff
NumberField.RingOfIntegers
Rat.ringOfIntegersEquiv
Rat.ringOfIntegersEquiv_apply_coe
Rat.ringOfIntegersEquiv_symm_apply_coe
IsCyclotomicExtension.integral
IsCyclotomicExtension.ringOfIntegers
```

The shortest stable route in this checkout is coefficientwise integrality
followed by `IsIntegrallyClosed.isIntegral_iff` for `ℤ ⊂ ℚ`. The
ring-of-integers equivalence was audited but does not introduce a duplicate
polynomial-lift API.

## B. Integral cyclotomic factor polynomials

The production module is:

```text
DkMath/NumberTheory/CyclotomicQRIntegralDescent.lean
```

For a primitive root `ζ`, `IsPrimitiveRoot.isIntegral` gives integrality of
`ζ`, and `IsIntegral.pow` gives integrality of every root power `ζ ^ a.val`.
The root factor is then handled coefficientwise by
`MvPolynomial.isIntegral_iff_isIntegral_coeff`; its only nonzero
coefficients are `1` and `-(ζ ^ a.val)`. Closure under finite products gives:

```text
rootFactorPoly_integral
qrFactorPoly_integral
qnrFactorPoly_integral
Rpoly_integral
Dpoly_sq_integral
```

The final two declarations have the forms:

```lean
IsIntegral (MvPolynomial (Fin 2) ℤ) (Rpoly (p := p) ζ)
IsIntegral (MvPolynomial (Fin 2) ℤ) (Dpoly (p := p) ζ ^ 2)
```

No elementary-symmetric expansion is used. The production file installs
`MvPolynomial.algebraMvPolynomial` locally so the coefficientwise integral
polynomial algebra is explicit and does not affect downstream global
instances.

## C. Descent from a rational Phase-10 coefficient

The reusable bridge is:

```text
isIntegral_rat_of_map_isIntegral
```

Given `hq : algebraMap ℚ L q = c` and `hc : IsIntegral ℤ c`, it applies
`isIntegral_algebraMap_iff` with
`FaithfulSMul.algebraMap_injective ℚ L`, using the standard scalar tower.
The Phase-10 witnesses are handled without uniqueness assumptions by:

```text
coeff_R0_isIntegral_int
coeff_D20_isIntegral_int
```

These use `MvPolynomial.coeff_map` to transport the Phase-10 map equality to
the already integral coefficient of `Rpoly` or `Dpoly ^ 2`.

## D. Rational integral elements are integer casts

The exact bridge is packaged as:

```text
rat_isIntegral_iff_exists_int
```

with statement:

```lean
IsIntegral ℤ q ↔ ∃ z : ℤ, (algebraMap ℤ ℚ) z = q
```

It is a direct specialization of the pinned
`IsIntegrallyClosed.isIntegral_iff` theorem. The coefficient range lemmas

```text
coeff_R0_mem_range_intCast
coeff_D20_mem_range_intCast
```

therefore provide `Set.range (algebraMap ℤ ℚ)` membership for every Phase-10
coefficient.

## E. Whole-polynomial integer descent

The final production theorems are:

```lean
theorem exists_Rpoly_over_int
    {L : Type*} [Field L] [Algebra ℚ L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p) :
    ∃ RZ : MvPolynomial (Fin 2) ℤ,
      MvPolynomial.map (algebraMap ℤ L) RZ = Rpoly (p := p) ζ

theorem exists_Dpoly_sq_over_int
    {L : Type*} [Field L] [Algebra ℚ L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p) :
    ∃ D2Z : MvPolynomial (Fin 2) ℤ,
      MvPolynomial.map (algebraMap ℤ L) D2Z = Dpoly (p := p) ζ ^ 2
```

Both proofs specialize the Phase-10 base-field existence theorem to
`K = ℚ`, apply `MvPolynomial.mem_range_map_iff_coeffs_subset`, and compose
`algebraMap ℤ ℚ` with `algebraMap ℚ L` using
`IsScalarTower.algebraMap_eq`. No chosen canonical witness is exported.

## F. Regression and compatibility

The focused test modules are:

```text
DkMathTest/FLT/Prime/CyclotomicQRIntegralDescentProbe.lean
DkMathTest/FLT/Prime/CyclotomicQRIntegralDescentCompatibility.lean
DkMathTest/FLT/Prime/CyclotomicQRIntegralDescentAxiomAudit.lean
```

The probe checks both integer descent theorems in
`CyclotomicField p ℚ` for:

```text
p = 3, 5, 7, 11, 13
```

The compatibility target retains the existing p=11 and p=13 chain:

```text
QR/QNR product → cyclotomic shell → TraceOne norm
```

The new integer witnesses remain abstract and are not identified with
`A11/B11` or `A13/B13`.

## G. Verification and axiom audit

The production module, probe, compatibility target, and API audit all build
successfully in the pinned checkout. The Phase-9/10 production chain and
`DkMath.FLT.Seven` are included in the final focused wrapper build.

The public declarations listed in the audit report only the inherited kernel
dependencies `propext`, `Classical.choice`, and `Quot.sound`. There is no
`sorryAx`, new `sorry`, or explicit `axiom` in the Phase-11 production and
test sources.

## Next boundary

```text
integral Gaussian-coordinate extraction / discriminant-square normalization
```

The next phase may address the stronger statement behind
`Dpoly^2 = D_p * S_p^2` with `S_p ∈ ℤ[X,Y]` and parity compatible with
`R_p - S_p = 2*A_p`. That work is explicitly outside Phase 11.
