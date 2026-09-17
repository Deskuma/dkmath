/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.ClassGroupTorsionBridge
import DkMath.FLT.Prime.PrimeTraceOneClassGroupClosure
import DkMath.FLT.Seven.QuadraticEuclidean
import DkMath.NumberTheory.PrimeTraceOneClassNumber
import DkMath.NumberTheory.PrimeQuadraticDiscriminant
import DkMath.NumberTheory.TraceOneQuadraticField
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.RingTheory.ClassGroup.ExtendedHom

#print "file: DkMathTest.FLT.Prime.PrimeTraceOneClassNumberFrontierApiAudit"

open scoped nonZeroDivisors

open DkMath.Lib.NumberTheory
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.NumberTheory.TraceOneQuadraticField
open Module NumberField InfinitePlace Ideal Nat

#check classGroupPTorsionFreeAt
#check classGroupPTorsionFreeAt_of_coprime_card

#check TraceOneRat
#check traceOneRat_ringOfIntegers_equiv
#check traceOneRat_isDedekindDomain
#check traceOneRat_numberField

#check signedPrimeDiscriminant
#check signedPrimeParameter
#check discr_signedPrimeParameter

#check NumberField.classNumber
#check NumberField.classNumber_pos
#check NumberField.classNumber_ne_zero
#check NumberField.classNumber_eq_one_iff
#check NumberField.exists_ideal_in_class_of_norm_le
#check ClassGroup.fintypeOfAdmissibleOfFinite

#check ClassGroup.mulEquiv
#check Fintype.card_congr
#check Nat.card_congr
#check NumberField.discr
#check NumberField.coe_discr
#check NumberField.discr_eq_discr
#check NumberField.discr_eq_discr_of_ringEquiv
#check NumberField.nrRealPlaces_eq_zero_iff
#check NumberField.nrComplexPlaces_eq_zero_iff
#check NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces
#check NumberField.InfinitePlace.card_add_two_mul_card_eq_rank
#check NumberField.IsTotallyReal.nrComplexPlaces_eq_zero
#check NumberField.IsTotallyComplex.nrRealPlaces_eq_zero
#check NumberField.IsTotallyReal.finrank
#check NumberField.IsTotallyComplex.finrank

#check ClassGroup.extendedHom
#check ClassGroup.extendedHom_mk0
#check ClassGroup.extendedHom_comp
#check ClassGroup.mulEquiv
#check NumberField.Ideal.tendsto_norm_le_and_mk_eq_div_atTop
#check NumberField.Ideal.tendsto_norm_le_div_atTop₀
#check NumberField.Ideal.tendsto_norm_le_div_atTop

#check DkMath.NumberTheory.traceOne_classGroup_card_eq_classNumber
#check DkMath.NumberTheory.classGroupPTorsionFreeAt_primeTraceOne_of_coprime_classNumber

example : signedPrimeParameter 7 = -2 := by
  norm_num [signedPrimeParameter, signedPrimeDiscriminant]

example : Fintype.card (ClassGroup (TraceOneInt (-2))) = 1 := by
  exact card_classGroup_eq_one

example : Nat.Coprime 7 (Fintype.card (ClassGroup (TraceOneInt (-2)))) := by
  rw [card_classGroup_eq_one]
  exact Nat.coprime_one_right 7

example : classGroupPTorsionFreeAt (TraceOneInt (-2)) 7 :=
  DkMath.FLT.Prime.classGroupPTorsionFreeAt_traceOneNegTwo_seven

example :
    let : Fact (∀ r : ℚ,
        r ^ 2 ≠ (signedPrimeParameter 7 : ℚ) + 1 * r) :=
      ⟨traceOneRat_no_rational_root Nat.prime_seven (by norm_num)⟩
    let : Field (TraceOneRat (signedPrimeParameter 7)) :=
      traceOneRatField Nat.prime_seven (by norm_num)
    let : NumberField (TraceOneRat (signedPrimeParameter 7)) := {
      to_charZero := charZero_of_injective_algebraMap (by
        intro q₁ q₂ hq
        have hre := congrArg QuadraticAlgebra.re hq
        change q₁ = q₂ at hre
        exact hre)
      to_finiteDimensional := inferInstance }
    let : IsDomain (TraceOneInt (signedPrimeParameter 7)) :=
      (traceOneRatHom_injective _).isDomain (traceOneRatHom _)
    let : IsDedekindDomain (TraceOneInt (signedPrimeParameter 7)) :=
      traceOneRat_isDedekindDomain Nat.prime_seven (by norm_num)
    let : IsIntegralClosure (TraceOneInt (signedPrimeParameter 7)) ℤ
        (TraceOneRat (signedPrimeParameter 7)) :=
      traceOneRat_isIntegralClosure Nat.prime_seven (by norm_num)
    let : Fintype (ClassGroup (TraceOneInt (signedPrimeParameter 7))) :=
      ClassGroup.fintypeOfAdmissibleOfFinite ℚ (TraceOneRat (signedPrimeParameter 7))
        AbsoluteValue.absIsAdmissible
    Fintype.card (ClassGroup (TraceOneInt (signedPrimeParameter 7))) =
      NumberField.classNumber (TraceOneRat (signedPrimeParameter 7)) := by
  exact DkMath.NumberTheory.traceOne_classGroup_card_eq_classNumber
    Nat.prime_seven (by norm_num)

example : signedPrimeParameter 11 = -3 := by
  norm_num [signedPrimeParameter, signedPrimeDiscriminant]

example : 11 % 4 = 3 := by norm_num
