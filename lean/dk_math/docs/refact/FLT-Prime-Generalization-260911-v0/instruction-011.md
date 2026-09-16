# FLT prime-generalization Phase 11 — integral coefficient descent

## Goal

Phase 10 proved whole-polynomial descent of `Rpoly ζ` and `Dpoly ζ ^ 2` from a cyclotomic extension to the base field.  This phase specializes the base field to `ℚ` and proves that the descended rational coefficients are in fact integers.

The target classification is:

```text
PGEN-GAUSS-ZDESCENT-GREEN
```

This phase **does not** construct the final Gaussian coordinate `S_p`, does not identify `Dpoly` itself with `√D_p * S_p`, does not alter FLT3/FLT5/FLT7 endpoints, and does not claim an FLT contradiction.

## Starting point

Use the production results from:

```text
DkMath.NumberTheory.CyclotomicQRCoefficientDescent
```

especially

```lean
exists_Rpoly_over_base
exists_Dpoly_sq_over_base
```

specialized to `K = ℚ`.

For a cyclotomic extension `L / ℚ`, primitive `p`-th root `ζ : L`, and Phase-10 witnesses

```lean
R0  : MvPolynomial (Fin 2) ℚ
D20 : MvPolynomial (Fin 2) ℚ
```

with

```lean
MvPolynomial.map (algebraMap ℚ L) R0  = Rpoly (p := p) ζ
MvPolynomial.map (algebraMap ℚ L) D20 = Dpoly (p := p) ζ ^ 2
```

prove that there exist integer polynomials

```lean
RZ  : MvPolynomial (Fin 2) ℤ
D2Z : MvPolynomial (Fin 2) ℤ
```

such that

```lean
MvPolynomial.map (algebraMap ℤ ℚ) RZ  = R0
MvPolynomial.map (algebraMap ℤ ℚ) D2Z = D20.
```

Equivalently, after mapping to `L`, they recover the original `Rpoly` and `Dpoly ^ 2`.

---

## Part A — pinned API audit first

Audit the pinned Mathlib checkout and record exact theorem names/signatures before implementation.  At minimum inspect:

```text
IsPrimitiveRoot.isIntegral
MvPolynomial.isIntegral_iff_isIntegral_coeff
IsIntegral.add
IsIntegral.sub
IsIntegral.mul
IsIntegral.pow
isIntegral_algebraMap_iff
IsIntegralClosure.isIntegral_iff
NumberField.RingOfIntegers
Rat.ringOfIntegersEquiv
Rat.ringOfIntegersEquiv_apply_coe
Rat.ringOfIntegersEquiv_symm_apply_coe
MvPolynomial.mem_range_map_iff_coeffs_subset
```

Also audit whether the pinned checkout provides a more direct theorem equivalent to

```text
q : ℚ, IsIntegral ℤ q  ->  ∃ z : ℤ, (z : ℚ) = q
```

for example through `IsIntegralClosure.isIntegral_iff`, `IsDedekindDomain.isIntegral_iff`, or the ring-of-integers equivalence.  Use the shortest stable pinned route.

Do not rely on current online Mathlib names if they differ from the pinned checkout.

---

## Part B — integrality of the cyclotomic QR/QNR factor polynomials

Create a production module, suggested path:

```text
DkMath/NumberTheory/CyclotomicQRIntegralDescent.lean
```

Import only the Phase-10 module plus the minimal pinned integrality / number-field files required.

For

```lean
{L : Type*} [Field L]
{p : ℕ} [Fact p.Prime]
(ζ : L) (hζ : IsPrimitiveRoot ζ p)
```

prove the root coefficient is integral over `ℤ`:

```lean
IsIntegral ℤ (ζ ^ a.val)
```

using `hζ.isIntegral Fact.out.pos` followed by `IsIntegral.pow`, or the exact pinned equivalent.

Then prove that the polynomial lifts have integral coefficients.  Preferred architecture:

```lean
qrFactorPoly_integral
qnrFactorPoly_integral
Rpoly_integral
Dpoly_sq_integral
```

where the final two statements are most usefully expressed either as

```lean
IsIntegral (MvPolynomial (Fin 2) ℤ) (Rpoly (p := p) ζ)
IsIntegral (MvPolynomial (Fin 2) ℤ) (Dpoly (p := p) ζ ^ 2)
```

or directly coefficientwise:

```lean
∀ d, IsIntegral ℤ (MvPolynomial.coeff d (Rpoly (p := p) ζ))
∀ d, IsIntegral ℤ (MvPolynomial.coeff d (Dpoly (p := p) ζ ^ 2))
```

Choose whichever form is cleanest in the pinned API.  `MvPolynomial.isIntegral_iff_isIntegral_coeff` is the preferred bridge if it compiles cleanly.

Important: do **not** prove coefficient integrality by expanding all elementary symmetric sums manually.  The root-of-unity integrality plus closure of integral elements under ring operations should carry the proof.

A ring-of-integers lift is also acceptable if it is shorter and more robust:

```text
ζ ∈ 𝓞 L
QR/QNR factor polynomial over 𝓞 L
map to L = existing factor polynomial
```

but do not introduce a duplicate parallel API unless it materially simplifies the proof.

---

## Part C — descend integrality from `L` to the Phase-10 rational coefficient

Specialize to

```lean
[Field L] [Algebra ℚ L]
```

with the standard `ℤ -> ℚ -> L` scalar tower.

Suppose

```lean
q : ℚ
hq : algebraMap ℚ L q = c
hc : IsIntegral ℤ c
```

prove

```lean
IsIntegral ℤ q.
```

Preferred route:

```lean
(isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective ℚ L)).mp ?_
```

or the exact pinned equivalent.  The required mapped integrality should use the scalar-tower identity between `algebraMap ℤ L` and `algebraMap ℚ L ∘ algebraMap ℤ ℚ`.

Package this as a reusable helper, e.g.

```lean
isIntegral_rat_of_map_isIntegral
```

with the weakest useful assumptions.

Then, for each coefficient of a Phase-10 witness `R0` / `D20`, use the map equality and `MvPolynomial.coeff_map` to identify its image in `L` with the corresponding integral coefficient of `Rpoly` / `Dpoly ^ 2`, and conclude that the rational coefficient is integral over `ℤ`.

Suggested statements:

```lean
coeff_R0_isIntegral_int
coeff_D20_isIntegral_int
```

Do not silently use uniqueness of Phase-10 witnesses; formulate these lemmas for any witness satisfying the required map equality.

---

## Part D — rational integral element is an integer

Prove or package the exact bridge

```lean
rat_isIntegral_iff_exists_int
    (q : ℚ) :
    IsIntegral ℤ q ↔ ∃ z : ℤ, (algebraMap ℤ ℚ) z = q
```

if an equivalent pinned theorem is not already directly usable.

Preferred sources, in order:

1. an existing direct pinned theorem;
2. `IsIntegralClosure.isIntegral_iff` for the integral closure of `ℤ` in `ℚ`;
3. `NumberField.RingOfIntegers ℚ` plus `Rat.ringOfIntegersEquiv`;
4. only as a last resort, a rational-root / integrally-closed proof.

Avoid denominator arithmetic unless all higher-level routes fail.

Use this to prove every coefficient of `R0` and `D20` belongs to

```lean
Set.range (algebraMap ℤ ℚ).
```

Suggested lemmas:

```lean
coeff_R0_mem_range_intCast
coeff_D20_mem_range_intCast
```

---

## Part E — whole-polynomial `ℤ` descent

Use

```lean
MvPolynomial.mem_range_map_iff_coeffs_subset
```

exactly as in Phase 10 to avoid manually assembling polynomial witnesses.

Prove production theorems of the shape:

```lean
theorem exists_Rpoly_over_int
    {L : Type*} [Field L] [Algebra ℚ L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p) :
    ∃ RZ : MvPolynomial (Fin 2) ℤ,
      MvPolynomial.map (algebraMap ℤ L) RZ = Rpoly (p := p) ζ
```

and

```lean
theorem exists_Dpoly_sq_over_int
    ... :
    ∃ D2Z : MvPolynomial (Fin 2) ℤ,
      MvPolynomial.map (algebraMap ℤ L) D2Z = Dpoly (p := p) ζ ^ 2.
```

If direct `algebraMap ℤ L` mapping is awkward because of typeclass/scalar-tower normalization, it is acceptable to first produce

```lean
map (algebraMap ℤ ℚ) RZ = R0
```

for a Phase-10 `R0`, then compose maps and prove the final equality to `L` separately.

Do not export a chosen polynomial using `Classical.choose` unless later phases genuinely require canonical names.  Existential production theorems are sufficient for this checkpoint.

---

## Part F — finite regression and compatibility

Add focused tests, suggested paths:

```text
DkMathTest/FLT/Prime/CyclotomicQRIntegralDescentProbe.lean
DkMathTest/FLT/Prime/CyclotomicQRIntegralDescentCompatibility.lean
DkMathTest/FLT/Prime/CyclotomicQRIntegralDescentAxiomAudit.lean
```

Specialize the production theorem to

```text
p = 3, 5, 7, 11, 13
L = CyclotomicField p ℚ
```

and verify both integer polynomial descent theorems.

For `p = 11, 13`, retain compatibility with the already proved chain

```text
QR/QNR product
  -> cyclotomic shell
  -> TraceOne norm
```

but do **not** yet identify the new integer polynomial witness with the explicit `A11/B11` or `A13/B13` coordinates.

Rebuild:

```text
DkMath.FLT.Seven
```

as a regression target.

---

## Part G — axiom and source audit

Run `#print axioms` on all new public production declarations.

Required outcome:

```text
no sorryAx
no new sorry
no explicit axiom
```

Kernel dependencies such as `propext`, `Classical.choice`, and `Quot.sound` are acceptable if inherited from Mathlib / finite-set infrastructure.

Also run:

```bash
git diff --check
```

and the repository's normal warning / forbidden-construct scans.

---

## Classification

Use exactly one of:

```text
PGEN-GAUSS-ZDESCENT-GREEN
PGEN-INTEGRALITY-MISSING-API
PGEN-INTEGRALITY-BOUNDARY
PGEN-INTEGRALITY-FAILED
```

`GREEN` requires both whole-polynomial integer descent theorems for arbitrary prime `p` in a cyclotomic extension over `ℚ`.

If GREEN, report the next boundary explicitly as:

```text
integral Gaussian-coordinate extraction / discriminant-square normalization
```

That next phase is expected to address the stronger statement behind

```text
Dpoly^2 = D_p * S_p^2
```

with `S_p ∈ ℤ[X,Y]` and parity compatible with

```text
R_p - S_p = 2*A_p.
```

Do not attempt that in Phase 11.

## Required report

Create:

```text
docs/refact/FLT-Prime-Generalization-260911-v0/report-011.md
```

The report must record:

- exact pinned integrality / ring-of-integers APIs used;
- whether the proof used coefficientwise integrality or an `𝓞_L` polynomial lift;
- the rational-integral-to-integer bridge;
- final theorem signatures;
- p=3/5/7/11/13 regressions;
- axiom audit;
- the exact next boundary.
