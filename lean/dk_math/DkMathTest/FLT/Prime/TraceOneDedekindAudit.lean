/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.TraceOneQuadraticField
import DkMath.Lib.NumberTheory.PrincipalIdealPower

#print "file: DkMathTest.FLT.Prime.TraceOneDedekindAudit"

open scoped nonZeroDivisors
open DkMath.Lib.NumberTheory
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.NumberTheory.TraceOneQuadraticField

namespace DkMathTest.FLT.Prime.TraceOneDedekindAudit

#check IsIntegralClosure.isDedekindDomain
#check NumberField.RingOfIntegers.equiv
#check exists_eq_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt

example {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    letI : Fact (∀ r : ℚ,
        r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
      ⟨traceOneRat_no_rational_root hp hp2⟩
    letI : Field (TraceOneRat (signedPrimeParameter p)) := inferInstance
    IsDedekindDomain (TraceOneInt (signedPrimeParameter p)) := by
  letI : Fact (∀ r : ℚ,
      r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
    ⟨traceOneRat_no_rational_root hp hp2⟩
  letI : Field (TraceOneRat (signedPrimeParameter p)) := inferInstance
  exact traceOneRat_isDedekindDomain hp hp2

example {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    letI : Fact (∀ r : ℚ,
        r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
      ⟨traceOneRat_no_rational_root hp hp2⟩
    letI : Field (TraceOneRat (signedPrimeParameter p)) := inferInstance
    Nonempty (NumberField.RingOfIntegers (TraceOneRat (signedPrimeParameter p))
      ≃+* TraceOneInt (signedPrimeParameter p)) :=
  traceOneRat_ringOfIntegers_equiv hp hp2

example {R : Type*} [CommRing R] [IsDedekindDomain R]
    {I : Ideal R} {a : R} {p : ℕ}
    (hI0 : I ∈ (Ideal R)⁰)
    (hfree : classGroupPTorsionFreeAt R p)
    (hunit : ∀ u : Rˣ, ∃ e : Rˣ, u = e ^ p)
    (hspan : Ideal.span ({a} : Set R) = I ^ p) :
    ∃ delta : R, a = delta ^ p := by
  exact exists_eq_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
    hI0 hfree hunit hspan

example {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    letI : Fact (∀ r : ℚ,
        r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
      ⟨traceOneRat_no_rational_root hp hp2⟩
    letI : Field (TraceOneRat (signedPrimeParameter p)) := inferInstance
    letI : IsDomain (TraceOneInt (signedPrimeParameter p)) :=
      (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
    letI : IsDedekindDomain (TraceOneInt (signedPrimeParameter p)) :=
      traceOneRat_isDedekindDomain hp hp2
    ∀ {I : Ideal (TraceOneInt (signedPrimeParameter p))}
      {a : TraceOneInt (signedPrimeParameter p)},
      I ∈ (Ideal (TraceOneInt (signedPrimeParameter p)))⁰ →
      classGroupPTorsionFreeAt (TraceOneInt (signedPrimeParameter p)) p →
      (∀ u : (TraceOneInt (signedPrimeParameter p))ˣ,
        ∃ e, u = e ^ p) →
      Ideal.span ({a} : Set (TraceOneInt (signedPrimeParameter p))) = I ^ p →
      ∃ delta : TraceOneInt (signedPrimeParameter p), a = delta ^ p := by
  letI : Fact (∀ r : ℚ,
      r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
    ⟨traceOneRat_no_rational_root hp hp2⟩
  letI : Field (TraceOneRat (signedPrimeParameter p)) := inferInstance
  letI : IsDomain (TraceOneInt (signedPrimeParameter p)) :=
    (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
  letI : IsDedekindDomain (TraceOneInt (signedPrimeParameter p)) :=
    traceOneRat_isDedekindDomain hp hp2
  intro I a hI0 hfree hunit hspan
  exact exists_eq_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
    hI0 hfree hunit hspan

example :
    letI : Field (TraceOneRat (signedPrimeParameter 3)) :=
      traceOneRatField (p := 3) (by norm_num) (by norm_num)
    IsDedekindDomain (TraceOneInt (signedPrimeParameter 3)) := by
  letI : Field (TraceOneRat (signedPrimeParameter 3)) :=
    traceOneRatField (p := 3) (by norm_num) (by norm_num)
  exact traceOneRat_isDedekindDomain (p := 3) (by norm_num) (by norm_num)

end DkMathTest.FLT.Prime.TraceOneDedekindAudit
