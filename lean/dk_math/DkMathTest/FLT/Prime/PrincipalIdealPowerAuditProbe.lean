/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.PrincipalIdealPower
import DkMath.FLT.Three.EisensteinCubeExtraction
import DkMath.FLT.Five.GoldenEuclidean
import DkMath.FLT.Seven.QuadraticCoprimeFactor
import DkMath.FLT.Seven.SevenRamifiedFusionElementLevelOrientedPower

#print "file: DkMathTest.FLT.Prime.PrincipalIdealPowerAuditProbe"

open scoped nonZeroDivisors
open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.FLT.Five

#synth IsDomain (TraceOneInt (-1))
#synth EuclideanDomain (TraceOneInt (-1))
#synth GCDMonoid (TraceOneInt (-1))
#synth IsPrincipalIdealRing (TraceOneInt (-1))
#synth IsDedekindDomain (TraceOneInt (-1))

#synth IsDomain GoldenInt
#synth EuclideanDomain GoldenInt
#synth IsPrincipalIdealRing GoldenInt
#synth IsDedekindDomain GoldenInt

#synth IsDomain (TraceOneInt (-2))
#synth EuclideanDomain (TraceOneInt (-2))
#synth GCDMonoid (TraceOneInt (-2))
#synth IsPrincipalIdealRing (TraceOneInt (-2))
#synth IsDedekindDomain (TraceOneInt (-2))

namespace DkMathTest.FLT.Prime.PrincipalIdealPowerAuditProbe

example {R : Type*} [CommRing R] [IsDomain R]
    {a b : R}
    (h : Ideal.span ({a} : Set R) = Ideal.span ({b} : Set R)) :
    Associated a b := by
  exact DkMath.Lib.NumberTheory.associated_of_span_singleton_eq_span_singleton h

example {R : Type*} [CommRing R] [IsDomain R]
    {I : Ideal R} {a : R} {p : ℕ}
    (hI : I.IsPrincipal)
    (hspan : Ideal.span ({a} : Set R) = I ^ p) :
    ∃ u gamma : R,
      IsUnit u ∧ Ideal.span ({gamma} : Set R) = I ∧ a = u * gamma ^ p := by
  exact
    DkMath.Lib.NumberTheory.exists_unit_mul_pow_of_span_eq_pow_of_isPrincipal
      hI hspan

example {R : Type*} [CommRing R] [IsDedekindDomain R]
    {I : Ideal R} {a : R} {p : ℕ}
    (hI0 : I ∈ (Ideal R)⁰)
    (hfree : DkMath.Lib.NumberTheory.classGroupPTorsionFreeAt R p)
    (hspan : Ideal.span ({a} : Set R) = I ^ p) :
    ∃ u gamma : R,
      IsUnit u ∧ Ideal.span ({gamma} : Set R) = I ∧ a = u * gamma ^ p := by
  exact
    DkMath.Lib.NumberTheory.exists_unit_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
      hI0 hfree hspan

example {R : Type*} [CommRing R] [IsDedekindDomain R]
    {I : Ideal R} {a : R} {p : ℕ}
    (hI0 : I ∈ (Ideal R)⁰)
    (hfree : DkMath.Lib.NumberTheory.classGroupPTorsionFreeAt R p)
    (hunit : ∀ u : Rˣ, ∃ e : Rˣ, u = e ^ p)
    (hspan : Ideal.span ({a} : Set R) = I ^ p) :
    ∃ delta : R, a = delta ^ p := by
  exact
    DkMath.Lib.NumberTheory.exists_eq_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
      hI0 hfree hunit hspan

example {I : Ideal (TraceOneInt (-1))} {a : TraceOneInt (-1)}
    (hI0 : I ∈ (Ideal (TraceOneInt (-1)))⁰)
    (hfree : DkMath.Lib.NumberTheory.classGroupPTorsionFreeAt
      (TraceOneInt (-1)) 3)
    (hspan : Ideal.span ({a} : Set (TraceOneInt (-1))) = I ^ 3) :
    ∃ u gamma : TraceOneInt (-1),
      IsUnit u ∧
        Ideal.span ({gamma} : Set (TraceOneInt (-1))) = I ∧
          a = u * gamma ^ 3 := by
  exact
    DkMath.Lib.NumberTheory.exists_unit_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
      hI0 hfree hspan

example {I : Ideal GoldenInt} {a : GoldenInt}
    (hI0 : I ∈ (Ideal GoldenInt)⁰)
    (hfree : DkMath.Lib.NumberTheory.classGroupPTorsionFreeAt GoldenInt 5)
    (hspan : Ideal.span ({a} : Set GoldenInt) = I ^ 5) :
    ∃ u gamma : GoldenInt,
      IsUnit u ∧ Ideal.span ({gamma} : Set GoldenInt) = I ∧ a = u * gamma ^ 5 := by
  exact
    DkMath.Lib.NumberTheory.exists_unit_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
      hI0 hfree hspan

example {I : Ideal (TraceOneInt (-2))} {a : TraceOneInt (-2)}
    (hI0 : I ∈ (Ideal (TraceOneInt (-2)))⁰)
    (hfree : DkMath.Lib.NumberTheory.classGroupPTorsionFreeAt
      (TraceOneInt (-2)) 7)
    (hspan : Ideal.span ({a} : Set (TraceOneInt (-2))) = I ^ 7) :
    ∃ u gamma : TraceOneInt (-2),
      IsUnit u ∧
        Ideal.span ({gamma} : Set (TraceOneInt (-2))) = I ∧
          a = u * gamma ^ 7 := by
  exact
    DkMath.Lib.NumberTheory.exists_unit_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
      hI0 hfree hspan

#check DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.unitMulPowOfSpanEqPow
#check DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.exists_mul_pow_of_span_eq_mul_pow

end DkMathTest.FLT.Prime.PrincipalIdealPowerAuditProbe
