# FLT prime-generalization Phase 10 — Galois fixed-field coefficient descent

## Scope and outcome

This report records the bounded implementation requested by
`instruction-010.md`. Starting from the Phase-9 full Galois invariance, the
coefficients of `Rpoly ζ` and `Dpoly ζ ^ 2` are shown to be fixed by every
cyclotomic algebra automorphism. The finite Galois fixed-field theorem then
places each coefficient in the range of `algebraMap K L`, and the
`MvPolynomial` coefficient-range criterion gives whole-polynomial witnesses
over `K`.

The resulting classification is:

```text
PGEN-GAUSS-QDESCENT-GREEN
```

The work stops at base-field descent. It does not prove integrality over
`ℤ`, construct integral Gaussian coordinates, alter FLT endpoints, or prove
an FLT contradiction.

## A. Pinned API audit and selected route

The audit module is:

```text
DkMathTest/FLT/Prime/CyclotomicQRCoefficientDescentAxiomAudit.lean
```

The exact coefficient/range APIs are:

```text
MvPolynomial.coeff_map
MvPolynomial.mem_range_map_iff_coeffs_subset
MvPolynomial.map_injective
```

The fixed-field APIs confirmed in the pinned checkout are:

```text
IntermediateField.mem_fixedField_iff
IsGalois.fixedField_top
IsGalois.fixedField_fixingSubgroup
IsGalois.mem_range_algebraMap_iff_fixed
IntermediateField.mem_bot
```

The production route uses `IntermediateField.mem_fixedField_iff` for the
explicit fixed-field coefficient lemmas, then uses
`IsGalois.mem_range_algebraMap_iff_fixed` for the range form. The latter is
the direct finite-Galois theorem matching the required coefficient output;
`IsGalois.fixedField_top` and `IntermediateField.mem_bot` were retained in
the audit as the equivalent fixed-field/bottom route.

The cyclotomic assumptions supply:

```text
IsCyclotomicExtension.isGalois
IsCyclotomicExtension.finiteDimensional
```

with the singleton `{p}` finite. No manually reproved Galois theorem is used.

## B. Generic coefficient-fixed lemma

The neutral production module is:

```text
DkMath/NumberTheory/CyclotomicQRCoefficientDescent.lean
```

It imports the Phase-9 realization module and the pinned Galois API. The
generic helper is:

```text
coeff_fixed_of_map_eq
```

For a ring homomorphism `σ : L →+* L`, polynomial invariance is converted to
coefficient invariance by one use of `MvPolynomial.coeff_map` and congruence.
The helper has no cyclotomic assumptions.

## C. Coefficients in the fixed field and base-field range

The public fixed-field lemmas are:

```text
coeff_Rpoly_mem_fixedField
coeff_Dpoly_sq_mem_fixedField
```

For an arbitrary Phase-9 ambient

```lean
[Field K] [Field L] [Algebra K L]
[Fact p.Prime]
[IsCyclotomicExtension {p} K L]
```

the Phase-9 invariance theorems are applied to every
`σ : L ≃ₐ[K] L`. Since `Gal(L/K)` is implemented by this same algebra
automorphism type, the coefficient-fixed helper supplies the hypotheses of
`IntermediateField.mem_fixedField_iff`.

The range lemmas are:

```text
coeff_Rpoly_mem_range_algebraMap
coeff_Dpoly_sq_mem_range_algebraMap
```

The finite-dimensional instance is supplied explicitly by
`IsCyclotomicExtension.finiteDimensional {p} K L`, and the Galois instance by
`IsCyclotomicExtension.isGalois {p} K L`. Thus the result does not silently
assume an algebraic closure or a stronger ambient field.

## D. Whole-polynomial base-field descent

The production existence theorems are:

```text
exists_Rpoly_over_base
exists_Dpoly_sq_over_base
```

They apply `MvPolynomial.mem_range_map_iff_coeffs_subset`. For each nonzero
coefficient in `MvPolynomial.coeffs`, the corresponding monomial coefficient
is supplied by the range lemmas above. The result is exactly:

```lean
∃ R0 : MvPolynomial (Fin 2) K,
  MvPolynomial.map (algebraMap K L) R0 = Rpoly (p := p) ζ

∃ D20 : MvPolynomial (Fin 2) K,
  MvPolynomial.map (algebraMap K L) D20 = Dpoly (p := p) ζ ^ 2
```

No noncomputable chosen witness is exported, so later developments are not
forced to depend on an avoidable `Classical.choose`. Uniqueness is not needed
for this checkpoint and was not added.

## E. Concrete cyclotomic regressions

The focused probe is:

```text
DkMathTest/FLT/Prime/CyclotomicQRCoefficientDescentProbe.lean
```

It specializes to `CyclotomicField p ℚ` and checks both whole-polynomial
descent witnesses and coefficient range membership for:

```text
p = 3, 5, 7, 11, 13
```

The existing p=11/p=13 compatibility target remains the already-proved
chain

```text
QR/QNR product → cyclotomic shell → TraceOne norm identity
```

and is rebuilt in this phase. The new descent witnesses remain abstract; no
identification with explicit `A11/B11` or `A13/B13` coordinates is claimed.

## F. Integrality boundary — audit only

The following pinned declarations were audited but not used to prove an
integrality theorem:

```text
IsCyclotomicExtension.integral
IsCyclotomicExtension.ringOfIntegers
Algebra.IsIntegral
IsIntegral
integralClosure
IsIntegralClosure.isIntegral_iff
IsIntegrallyClosed.isIntegral_iff
Rat.ringOfIntegersEquiv
Rat.ringOfIntegersEquiv_apply_coe
```

The generic cyclotomic extension API supplies algebraic integrality, and the
number-field API supplies the ring-of-integers bridge for cyclotomic
extensions over `ℚ`. The exact coefficient statement “base-field rational and
algebraic integer implies integer” is not proved here.

The next boundary is therefore:

```text
PGEN-INTEGRALITY-API-READY
```

The following remain open:

```text
integrality over ℤ                 [NOT YET]
integral Gaussian coordinates      [NOT YET]
FLT descent / contradiction        [NOT YET]
```

## G. Verification and axiom audit

The focused targets were built successfully:

```text
lake build DkMath.NumberTheory.CyclotomicQRGaloisAction
lake build DkMath.NumberTheory.CyclotomicQRGaloisRealization
lake build DkMath.NumberTheory.CyclotomicQRCoefficientDescent
lake build DkMathTest.FLT.Prime.CyclotomicQRCoefficientDescentProbe
lake build DkMathTest.FLT.Prime.CyclotomicQRCoefficientDescentAxiomAudit
lake build DkMathTest.FLT.Prime.CyclotomicQRGaloisActionCompatibility
lake build DkMathTest.FLT.Prime.CyclotomicQRProductCompatibility
lake build DkMath.FLT.Seven
```

The new public declarations have focused `#print axioms` coverage. Their
reported dependencies are only `propext`, `Classical.choice`, and
`Quot.sound`; no `sorryAx` is present. The new production and test sources
contain no `sorry` and no explicit `axiom`.

The final closeout also includes `git diff --check`, a fresh warning scan, and
source scans for `sorry`, `sorryAx`, and explicit `axiom`.
