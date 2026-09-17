# FPTC-007 report — prime-discriminant class-number frontier

## Outcome

```text
Outcome C — CLASS-NUMBER FRONTIER ISOLATED
```

The class-number/CardGroup cardinality transport is green, and the concrete
coprimality-to-torsion bridge is green.  The current checked Minkowski and
ideal-counting APIs do not prove the required uniform coprimality for the
generic imaginary prime-discriminant family.  No general PID claim or class
number estimate was added.

## 1. Exact class-number and class-group APIs

The focused audit confirms:

```text
NumberField.classNumber K : ℕ
NumberField.classNumber_pos : 0 < NumberField.classNumber K
NumberField.classNumber_ne_zero : NumberField.classNumber K ≠ 0
NumberField.classNumber_eq_one_iff : classNumber K = 1 ↔ IsPrincipalIdealRing (𝓞 K)
NumberField.exists_ideal_in_class_of_norm_le C
  : ∃ I, ClassGroup.mk0 I = C ∧ absNorm I ≤ M K
```

The class number is definitionally
`Fintype.card (ClassGroup (NumberField.RingOfIntegers K))`.
For the TraceOne order, finiteness is supplied explicitly by
`ClassGroup.fintypeOfAdmissibleOfFinite ℚ K AbsoluteValue.absIsAdmissible`
after installing the existing `traceOneRat_isIntegralClosure` theorem.

For transport, the pinned Mathlib API provides:

```text
ClassGroup.mulEquiv (g : R ≃+* R') : ClassGroup R ≃* ClassGroup R'
Fintype.card_congr (e : α ≃ β) : Fintype.card α = Fintype.card β
Nat.card_congr (e : α ≃ β) : Nat.card α = Nat.card β
```

`ClassGroup.extendedHom` and its composition lemmas were also audited, but are
not needed: `ClassGroup.mulEquiv` is the direct ring-equivalence route.

## 2. RingOfIntegers to TraceOne transport

This part is green.  The new neutral theorem is:

```lean
traceOne_classGroup_card_eq_classNumber
    (hp : p.Prime) (hp2 : p ≠ 2) :
  Fintype.card (ClassGroup (TraceOneInt (signedPrimeParameter p))) =
    NumberField.classNumber (TraceOneRat (signedPrimeParameter p))
```

The actual theorem statement retains the necessary local `Fact`, `Field`,
`NumberField`, `IsDomain`, `IsDedekindDomain`, `IsIntegralClosure`, and
`Fintype` bindings.  Its proof obtains
`traceOneRat_ringOfIntegers_equiv`, applies `ClassGroup.mulEquiv`, and closes
the cardinality equality with `Fintype.card_congr`.  No quotient-level class
group transport was invented.

The follow-up bridge is also green:

```lean
classGroupPTorsionFreeAt_primeTraceOne_of_coprime_classNumber
    (hp : p.Prime) (hp2 : p ≠ 2) :
  Nat.Coprime p (NumberField.classNumber (TraceOneRat (signedPrimeParameter p))) →
    classGroupPTorsionFreeAt (TraceOneInt (signedPrimeParameter p)) p
```

It composes the equality above with the existing neutral theorem
`classGroupPTorsionFreeAt_of_coprime_card`.

## 3. Discriminant and signature audit

The currently checked TraceOne-side discriminant identity is:

```text
TraceOneQuadratic.discr (signedPrimeParameter p) = signedPrimeDiscriminant p
```

The existing ring-of-integers facts are:

```text
traceOneRat_isIntegralClosure
traceOneRat_ringOfIntegers_equiv
```

Mathlib exposes the number-field basis APIs
`NumberField.coe_discr`, `NumberField.discr_eq_discr`, and
`NumberField.discr_eq_discr_of_ringEquiv`.  However, the current repository
does not contain a checked theorem identifying

```text
NumberField.discr (TraceOneRat (signedPrimeParameter p))
  = signedPrimeDiscriminant p
```

The missing step is an explicit integral-basis/discriminant computation for the
TraceOne coordinate basis.  The order equivalence alone is not silently used
as a number-field discriminant equality.

For signatures, the existing `traceOnePrimeReal_signature` proves, for
`p % 4 = 1`,

```text
finrank ℚ K_p = 2 ∧ nrComplexPlaces K_p = 0 ∧ nrRealPlaces K_p = 2
```

The generic APIs `card_add_two_mul_card_eq_rank`,
`nrRealPlaces_eq_zero_iff`, `nrComplexPlaces_eq_zero_iff`, and the
`IsTotallyComplex`/`IsTotallyReal` consequences were audited.  No reusable
production theorem currently proves the required imaginary implication
`p % 4 = 3 → nrRealPlaces K_p = 0 → nrComplexPlaces K_p = 1` for this
TraceOne family.  `QuadraticAlgebra.finrank_eq_two` is available, but it does
not by itself establish the imaginary signature.

## 4. Minkowski APIs found

The exact class-by-class theorem is:

```text
NumberField.exists_ideal_in_class_of_norm_le
```

It supplies an integral ideal representative in every class with norm at most

```text
(4 / π) ^ nrComplexPlaces K *
  ((finrank ℚ K)! / (finrank ℚ K) ^ finrank ℚ K * √|NumberField.discr K|).
```

The repository also audited:

```text
NumberField.Ideal.tendsto_norm_le_and_mk_eq_div_atTop
NumberField.Ideal.tendsto_norm_le_div_atTop₀
NumberField.Ideal.tendsto_norm_le_div_atTop
```

These are asymptotic ideal-counting statements.  The existing
`RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt` is a conditional PID
criterion, not a class-number bound.

## 5. Minkowski conclusion

The available theorem gives existence of one small ideal representative per
class.  The checked API does not provide the required finite target together
with an injection or counting argument that would imply

```text
NumberField.classNumber K_p < p
```

or directly

```text
Nat.Coprime p (NumberField.classNumber K_p).
```

The asymptotic ideal-counting results do not supply this finite uniform bound.
Consequently no new ideal-counting/asymptotic library was introduced.

## 6. p=7 regression

The audit confirms:

```text
signedPrimeParameter 7 = -2
Fintype.card (ClassGroup (TraceOneInt (-2))) = 1
Nat.Coprime 7 (Fintype.card (ClassGroup (TraceOneInt (-2))))
classGroupPTorsionFreeAt (TraceOneInt (-2)) 7
```

The new class-number transport theorem was instantiated at `p = 7`, while the
existing `TraceOneInt (-2)` Euclidean/PID theorem remains the production
structural discharge.  The shorter FPTC-000 theorem was not replaced.

## 7. p=11 audit

The concrete normalization is checked:

```text
11 % 4 = 3
signedPrimeParameter 11 = -3
```

The first missing checked theorem for the p=11 branch is:

```text
Nat.Coprime 11
  (NumberField.classNumber (TraceOneRat (-3)))
```

with the existing `traceOneRatField`/`NumberField` instances.  Therefore p=11
remains conditional; no specialized Euclidean-domain development was added.

## 8. Strongest generic theorem proved

The strongest new generic arithmetic statement is the exact conditional bridge

```text
Nat.Coprime p (NumberField.classNumber K_p)
  → classGroupPTorsionFreeAt R_p p
```

where

```text
K_p = TraceOneRat (signedPrimeParameter p)
R_p = TraceOneInt (signedPrimeParameter p).
```

Together with the existing FPTC-004/FPTC-007 generic receiver, this exposes
the exact hypothesis needed by the imaginary residual route.  It does not
produce the hypothesis uniformly.

## 9. First remaining mathematical obstruction

The open arithmetic target is explicitly:

```text
∀ p : ℕ, p.Prime → p % 4 = 3 →
  Nat.Coprime p
    (NumberField.classNumber (TraceOneRat (signedPrimeParameter p))).
```

The next required mathematical input is a checked class-number coprimality
theorem for this imaginary prime-discriminant family, or a checked finite
ideal-counting argument strong enough to imply it.  Neither is present in the
current repository or the pinned Mathlib API.

## Validation and boundaries

Focused builds passed for the new production module, the API audit, and the
axiom audit, together with the required existing dependencies:

```text
lake build DkMath.Lib.NumberTheory.ClassGroupTorsionBridge
lake build DkMath.NumberTheory.TraceOneQuadraticField
lake build DkMath.FLT.Prime.PrimeTraceOneConditionalDescent
lake build DkMath.FLT.Prime.PrimeTraceOneCoordinateReceiver
lake build DkMath.NumberTheory.PrimeTraceOneClassNumber
lake build DkMathTest.FLT.Prime.PrimeTraceOneClassNumberFrontierApiAudit
lake build DkMathTest.FLT.Prime.PrimeTraceOneClassNumberFrontierAxiomAudit
```

The new production module is FLT-independent.  No general FLT theorem,
uniform PID claim, unproved class-number formula, analytic estimate, sector
elimination, or completed FLT contradiction is used.  No new `sorry`,
`sorryAx`, `admit`, explicit project axiom, or `unsafe` declaration is added.
