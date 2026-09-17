/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.ClassGroupTorsionBridge
import DkMath.NumberTheory.TraceOneQuadraticField
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.PrimeTraceOneClassNumber"

namespace DkMath.NumberTheory

open DkMath.Lib.NumberTheory
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.NumberTheory.TraceOneQuadraticField
open Module NumberField

noncomputable section

/-- The TraceOne class group has the same cardinality as the number-field
class group of its rational quadratic companion. -/
theorem traceOne_classGroup_card_eq_classNumber
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    let : Fact (∀ r : ℚ,
        r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
      ⟨traceOneRat_no_rational_root hp hp2⟩
    let : Field (TraceOneRat (signedPrimeParameter p)) :=
      traceOneRatField hp hp2
    let : NumberField (TraceOneRat (signedPrimeParameter p)) := {
      to_charZero := charZero_of_injective_algebraMap (by
        intro q₁ q₂ hq
        have hre := congrArg QuadraticAlgebra.re hq
        change q₁ = q₂ at hre
        exact hre)
      to_finiteDimensional := inferInstance }
    let : IsDomain (TraceOneInt (signedPrimeParameter p)) :=
      (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
    let : IsDedekindDomain (TraceOneInt (signedPrimeParameter p)) :=
      traceOneRat_isDedekindDomain hp hp2
    let : IsIntegralClosure (TraceOneInt (signedPrimeParameter p)) ℤ
        (TraceOneRat (signedPrimeParameter p)) :=
      traceOneRat_isIntegralClosure hp hp2
    let : Fintype (ClassGroup (TraceOneInt (signedPrimeParameter p))) :=
      ClassGroup.fintypeOfAdmissibleOfFinite ℚ (TraceOneRat (signedPrimeParameter p))
        AbsoluteValue.absIsAdmissible
    Fintype.card (ClassGroup (TraceOneInt (signedPrimeParameter p))) =
      NumberField.classNumber (TraceOneRat (signedPrimeParameter p)) := by
  let : Fact (∀ r : ℚ,
      r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
    ⟨traceOneRat_no_rational_root hp hp2⟩
  let instField : Field (TraceOneRat (signedPrimeParameter p)) :=
    traceOneRatField hp hp2
  let : Field (TraceOneRat (signedPrimeParameter p)) := instField
  let : NumberField (TraceOneRat (signedPrimeParameter p)) := {
    to_charZero := charZero_of_injective_algebraMap (by
      intro q₁ q₂ hq
      have hre := congrArg QuadraticAlgebra.re hq
      change q₁ = q₂ at hre
      exact hre)
    to_finiteDimensional := inferInstance }
  let : IsDomain (TraceOneInt (signedPrimeParameter p)) :=
    (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
  let : IsDedekindDomain (TraceOneInt (signedPrimeParameter p)) :=
    traceOneRat_isDedekindDomain hp hp2
  let : IsIntegralClosure (TraceOneInt (signedPrimeParameter p)) ℤ
      (TraceOneRat (signedPrimeParameter p)) :=
    traceOneRat_isIntegralClosure hp hp2
  let : Fintype (ClassGroup (TraceOneInt (signedPrimeParameter p))) :=
    ClassGroup.fintypeOfAdmissibleOfFinite ℚ (TraceOneRat (signedPrimeParameter p))
      AbsoluteValue.absIsAdmissible
  obtain ⟨e⟩ := traceOneRat_ringOfIntegers_equiv hp hp2
  have hcard := Fintype.card_congr (ClassGroup.mulEquiv e).toEquiv
  simpa only [NumberField.classNumber] using hcard.symm

/-- Coprimality with the concrete number-field class number supplies the
finite-class-group torsion hypothesis for the TraceOne route. -/
theorem classGroupPTorsionFreeAt_primeTraceOne_of_coprime_classNumber
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    let : Fact (∀ r : ℚ,
        r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
      ⟨traceOneRat_no_rational_root hp hp2⟩
    let : Field (TraceOneRat (signedPrimeParameter p)) :=
      traceOneRatField hp hp2
    let : NumberField (TraceOneRat (signedPrimeParameter p)) := {
      to_charZero := charZero_of_injective_algebraMap (by
        intro q₁ q₂ hq
        have hre := congrArg QuadraticAlgebra.re hq
        change q₁ = q₂ at hre
        exact hre)
      to_finiteDimensional := inferInstance }
    let : IsDomain (TraceOneInt (signedPrimeParameter p)) :=
      (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
    let : IsDedekindDomain (TraceOneInt (signedPrimeParameter p)) :=
      traceOneRat_isDedekindDomain hp hp2
    let : IsIntegralClosure (TraceOneInt (signedPrimeParameter p)) ℤ
        (TraceOneRat (signedPrimeParameter p)) :=
      traceOneRat_isIntegralClosure hp hp2
    let : Fintype (ClassGroup (TraceOneInt (signedPrimeParameter p))) :=
      ClassGroup.fintypeOfAdmissibleOfFinite ℚ (TraceOneRat (signedPrimeParameter p))
        AbsoluteValue.absIsAdmissible
    Nat.Coprime p (NumberField.classNumber (TraceOneRat (signedPrimeParameter p))) →
      classGroupPTorsionFreeAt (TraceOneInt (signedPrimeParameter p)) p := by
  let : Fact (∀ r : ℚ,
      r ^ 2 ≠ (signedPrimeParameter p : ℚ) + 1 * r) :=
    ⟨traceOneRat_no_rational_root hp hp2⟩
  let instField : Field (TraceOneRat (signedPrimeParameter p)) :=
    traceOneRatField hp hp2
  let : Field (TraceOneRat (signedPrimeParameter p)) := instField
  let : NumberField (TraceOneRat (signedPrimeParameter p)) := {
    to_charZero := charZero_of_injective_algebraMap (by
      intro q₁ q₂ hq
      have hre := congrArg QuadraticAlgebra.re hq
      change q₁ = q₂ at hre
      exact hre)
    to_finiteDimensional := inferInstance }
  let : IsDomain (TraceOneInt (signedPrimeParameter p)) :=
    (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
  let : IsDedekindDomain (TraceOneInt (signedPrimeParameter p)) :=
    traceOneRat_isDedekindDomain hp hp2
  let : IsIntegralClosure (TraceOneInt (signedPrimeParameter p)) ℤ
      (TraceOneRat (signedPrimeParameter p)) :=
    traceOneRat_isIntegralClosure hp hp2
  let : Fintype (ClassGroup (TraceOneInt (signedPrimeParameter p))) :=
    ClassGroup.fintypeOfAdmissibleOfFinite ℚ (TraceOneRat (signedPrimeParameter p))
      AbsoluteValue.absIsAdmissible
  dsimp
  intro hcop
  apply classGroupPTorsionFreeAt_of_coprime_card
  rw [traceOne_classGroup_card_eq_classNumber hp hp2]
  exact hcop

end

end DkMath.NumberTheory
