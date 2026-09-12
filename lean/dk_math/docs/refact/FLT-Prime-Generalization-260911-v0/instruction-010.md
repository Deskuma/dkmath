# FLT prime-generalization Phase 10 — Galois fixed-field coefficient descent

## Goal

Starting from Phase 9 (`PGEN-GAUSS-GALOIS-GREEN`), descend the coefficients of

```text
Rpoly ζ
Dpoly ζ ^ 2
```

from the cyclotomic extension `L` to the base field `K`.

This phase must stop at **base-field coefficient descent**.  Do not prove
integrality over `ℤ`, do not construct arbitrary-prime integral Gaussian
coordinates, and do not modify FLT3/FLT5/FLT7 endpoints.

Target classification on full success:

```text
PGEN-GAUSS-QDESCENT-GREEN
```

(`QDESCENT` means fixed-field/base-field descent; the production theorem may
remain generic in `K` rather than being restricted to `ℚ`.)

---

## Existing inputs

Use the production results already proved in:

```text
DkMath.NumberTheory.CyclotomicQRGaloisAction
DkMath.NumberTheory.CyclotomicQRGaloisRealization
```

In particular:

```text
map_Rpoly_of_cyclotomicAut
map_Dpoly_sq_of_cyclotomicAut
```

For every `σ : L ≃ₐ[K] L` these give invariance of `Rpoly ζ` and
`Dpoly ζ ^ 2` under coefficientwise `MvPolynomial.map`.

Do not reprove the QR/QNR action or automorphism realization.

---

## A. Audit the pinned fixed-field and MvPolynomial APIs

Confirm the exact signatures available in the pinned Mathlib checkout for at
least the following families:

```text
MvPolynomial.coeff_map
MvPolynomial.mem_range_map_iff_coeffs_subset
MvPolynomial.map_injective

IntermediateField.mem_fixedField_iff
IsGalois.fixedField_top
IsGalois.fixedField_fixingSubgroup

IsCyclotomicExtension.isGalois
```

Also audit whichever theorem gives membership in the bottom intermediate field
as membership in / existence from the range of `algebraMap K L`.

Do not guess theorem names.  Record the exact API actually used in
`report-010.md`.

---

## B. Generic coefficient-fixed lemma

Create a small neutral lemma, preferably in a new production module

```text
DkMath/NumberTheory/CyclotomicQRCoefficientDescent.lean
```

that extracts coefficientwise invariance from polynomial invariance.

Suggested shape (adapt to the pinned API):

```lean
theorem coeff_fixed_of_map_eq
    {K L : Type*} [CommSemiring K] [CommSemiring L]
    (σ : L →+* L) {P : MvPolynomial (Fin 2) L}
    (hP : MvPolynomial.map σ P = P)
    (d : Fin 2 →₀ ℕ) :
    σ (MvPolynomial.coeff d P) = MvPolynomial.coeff d P
```

This should be a thin use of `MvPolynomial.coeff_map` / congruence.

No cyclotomic assumptions belong in this helper.

---

## C. Coefficients lie in the fixed field

Work in the Phase-9 ambient:

```lean
{K L : Type*}
[Field K] [Field L] [Algebra K L]
{p : ℕ} [Fact p.Prime]
[IsCyclotomicExtension {p} K L]
(ζ : L) (hζ : IsPrimitiveRoot ζ p)
```

Add whatever finite-dimensional / Galois assumptions are actually required by
the pinned fixed-field theorem.  Prefer obtaining them from the cyclotomic
extension API when available; otherwise state them explicitly rather than
silently strengthening the ambient.

For every monomial exponent `d`, prove:

```text
coeff d (Rpoly ζ)
```

is fixed by every `σ : L ≃ₐ[K] L`, hence belongs to the fixed field of the full
Galois group.

Do the same for:

```text
coeff d (Dpoly ζ ^ 2)
```

Suggested public theorem family:

```text
coeff_Rpoly_mem_fixedField
coeff_Dpoly_sq_mem_fixedField
```

Then use the full-Galois fixed-field theorem to conclude that each coefficient
comes from the base field.

Suggested public output shape:

```lean
theorem coeff_Rpoly_mem_range_algebraMap ... (d : Fin 2 →₀ ℕ) :
    MvPolynomial.coeff d (Rpoly (p := p) ζ) ∈
      Set.range (algebraMap K L)

theorem coeff_Dpoly_sq_mem_range_algebraMap ... (d : Fin 2 →₀ ℕ) :
    MvPolynomial.coeff d (Dpoly (p := p) ζ ^ 2) ∈
      Set.range (algebraMap K L)
```

If the pinned API naturally returns an element of `⊥ : IntermediateField K L`
instead, keep that intermediate theorem too, but expose a range form suitable
for `MvPolynomial.mem_range_map_iff_coeffs_subset`.

---

## D. Descend the whole polynomials to the base field

Use coefficientwise range membership and
`MvPolynomial.mem_range_map_iff_coeffs_subset` (or the exact pinned equivalent)
to prove existence of base-field polynomials:

```lean
theorem exists_Rpoly_over_base ... :
    ∃ R0 : MvPolynomial (Fin 2) K,
      MvPolynomial.map (algebraMap K L) R0 = Rpoly (p := p) ζ

theorem exists_Dpoly_sq_over_base ... :
    ∃ D20 : MvPolynomial (Fin 2) K,
      MvPolynomial.map (algebraMap K L) D20 = Dpoly (p := p) ζ ^ 2
```

If convenient, also define noncomputable chosen witnesses:

```text
RpolyBase
DpolySqBase
```

but do not make later proofs depend on choice unless it materially simplifies
the API.

A stronger uniqueness theorem is optional and should be included only if it is
a direct consequence of `MvPolynomial.map_injective` and injectivity of the
field algebra map.

---

## E. Concrete `ℚ` cyclotomic-field specialization

Add a focused test module, for example:

```text
DkMathTest/FLT/Prime/CyclotomicQRCoefficientDescentProbe.lean
```

Specialize to:

```text
CyclotomicField p ℚ
```

and verify the descent theorem for

```text
p = 3, 5, 7, 11, 13.
```

For `p = 11, 13`, connect the descended objects back to the existing chain only
at the already-proved level:

```text
QR/QNR product
  -> cyclotomic shell
  -> existing TraceOne norm identity
```

Do not claim that the descended `R0` / `D20` have yet been identified with the
explicit `A11/B11` or `A13/B13` coordinates.

---

## F. Integrality boundary — audit only

Audit, but do not implement, the next step needed to descend from `ℚ` to `ℤ`.
Record exact pinned APIs for:

```text
IsCyclotomicExtension.integral
IsCyclotomicExtension.ringOfIntegers
Algebra.IsIntegral / IsIntegral
integralClosure
Rat / Int algebraic-integer intersection results
```

The next desired mathematical statement is:

```text
coefficients of Rpoly and Dpoly^2 are algebraic integers,
and after Phase 10 they lie in ℚ,
therefore they lie in ℤ.
```

Do not assert this unless it is formally proved in a later phase.

Classify the next boundary precisely as one of:

```text
PGEN-INTEGRALITY-API-READY
PGEN-INTEGRALITY-DERIVABLE
PGEN-INTEGRALITY-MISSING
```

---

## G. Axiom audit and verification

Add focused tests / audit modules for all new public production declarations.
Run at minimum:

```text
lake build DkMath.NumberTheory.CyclotomicQRGaloisAction
lake build DkMath.NumberTheory.CyclotomicQRGaloisRealization
lake build DkMath.NumberTheory.CyclotomicQRCoefficientDescent
lake build DkMathTest.FLT.Prime.CyclotomicQRCoefficientDescentProbe
lake build DkMathTest.FLT.Prime.CyclotomicQRCoefficientDescentAxiomAudit
lake build DkMath.FLT.Seven
```

Also run the existing p=11/13 compatibility targets touched by the import
closure.

Requirements:

```text
no sorry
no sorryAx
no new explicit axiom
git diff --check green
```

Report any unavoidable assumptions exactly.

---

## H. Report

Create:

```text
docs/refact/FLT-Prime-Generalization-260911-v0/report-010.md
```

The report must distinguish clearly:

```text
full Galois invariance             [Phase 9 GREEN]
coefficient fixed-field descent    [this phase]
base-field polynomial existence    [this phase]
integrality over ℤ                 [NOT YET]
integral Gaussian coordinates      [NOT YET]
FLT descent / contradiction        [NOT YET]
```

If the whole-polynomial base-field descent succeeds, classify:

```text
PGEN-GAUSS-QDESCENT-GREEN
```

Otherwise stop at the strongest proved sub-classification and identify the
first exact missing theorem.