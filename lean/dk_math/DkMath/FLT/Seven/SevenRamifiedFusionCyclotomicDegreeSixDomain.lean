/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionDegreeSixOrientedLoadFactorization
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.Localization.FractionRing

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicDegreeSixDomain"

namespace DkMath.FLT.Seven

noncomputable section

open scoped QuadraticAlgebra

namespace SevenCyclotomicDegreeSixInt

open SevenRealCubicInt

/-- Fraction field of the already identified real cubic maximal order. -/
private abbrev RealFrac : Type :=
  FractionRing SevenRealCubicInt

/-- The quadratic carrier after extension to the real cubic fraction field. -/
private abbrev FractionCarrier : Type :=
  QuadraticAlgebra RealFrac
    (-1)
    (algebraMap SevenRealCubicInt RealFrac (alpha - 1))

private theorem realFrac_trace_cubic_relation :
    (algebraMap SevenRealCubicInt RealFrac (alpha - 1)) ^ 3 +
        (algebraMap SevenRealCubicInt RealFrac (alpha - 1)) ^ 2 -
        2 * algebraMap SevenRealCubicInt RealFrac (alpha - 1) - 1 = 0 := by
  simpa only [map_add, map_sub, map_mul, map_pow, map_ofNat,
    map_one, map_zero] using
      congrArg (algebraMap SevenRealCubicInt RealFrac)
        alphaSubOne_cubic_relation

private theorem seventh_pow_eq_one_of_quadratic_realTrace_frac
    (z t : RealFrac)
    (hq : z ^ 2 - t * z + 1 = 0)
    (ht : t ^ 3 + t ^ 2 - 2 * t - 1 = 0) :
    z ^ 7 = 1 := by
  linear_combination
    (t ^ 5 + t ^ 4 * z + t ^ 3 * z ^ 2 - 4 * t ^ 3 +
      t ^ 2 * z ^ 3 - 3 * t ^ 2 * z + t * z ^ 4 -
      2 * t * z ^ 2 + 3 * t + z ^ 5 - z ^ 3 + z) * hq +
    (t ^ 3 * z - t ^ 2 * z - t ^ 2 - 2 * t * z +
      t + z + 1) * ht

private theorem realFrac_root_ne_one
    (z : RealFrac)
    (hz :
      z ^ 2 =
        -1 +
          algebraMap SevenRealCubicInt RealFrac (alpha - 1) * z) :
    z ≠ 1 := by
  intro hone
  subst z
  have htrace :
      algebraMap SevenRealCubicInt RealFrac (alpha - 1) = 2 := by
    linear_combination -hz
  have htrace' :
      algebraMap SevenRealCubicInt RealFrac (alpha - 1) =
        algebraMap SevenRealCubicInt RealFrac (2 : SevenRealCubicInt) := by
    simpa only [map_ofNat] using htrace
  have hbase :
      alpha - 1 = (2 : SevenRealCubicInt) :=
    (IsFractionRing.injective SevenRealCubicInt RealFrac) htrace'
  have halpha : alpha = (3 : SevenRealCubicInt) := by
    linear_combination hbase
  have hsnd := congrArg SevenRealCubicInt.snd halpha
  change (1 : ℤ) = 0 at hsnd
  omega

private theorem realFrac_root_isPrimitiveRoot
    (z : RealFrac)
    (hz :
      z ^ 2 =
        -1 +
          algebraMap SevenRealCubicInt RealFrac (alpha - 1) * z) :
    IsPrimitiveRoot z 7 := by
  have hq :
      z ^ 2 -
          algebraMap SevenRealCubicInt RealFrac (alpha - 1) * z +
          1 = 0 := by
    linear_combination hz
  have hpow : z ^ 7 = 1 :=
    seventh_pow_eq_one_of_quadratic_realTrace_frac
      z
      (algebraMap SevenRealCubicInt RealFrac (alpha - 1))
      hq realFrac_trace_cubic_relation
  refine ⟨hpow, ?_⟩
  intro l hl
  by_contra hnot
  have hcop : Nat.Coprime 7 l :=
    (Nat.Prime.coprime_iff_not_dvd
      (by norm_num : Nat.Prime 7)).mpr hnot
  have hone :
      z = 1 :=
    (pow_eq_one_iff_of_coprime hcop).mp
      ⟨hpow, hl⟩
  exact realFrac_root_ne_one z hz hone

/-- The real cubic fraction field cannot contain a root of the quadratic
relation defining the degree-six carrier. Such a root would be a primitive
seventh root of unity in a degree-three number field. -/
private theorem realFrac_quadratic_has_no_root :
    ∀ z : RealFrac,
      z ^ 2 ≠
        -1 +
          algebraMap SevenRealCubicInt RealFrac (alpha - 1) * z := by
  intro z hz
  have hprimFrac := realFrac_root_isPrimitiveRoot z hz
  let e :
      RealFrac ≃+* SevenRealCubic.Field :=
    IsFractionRing.ringEquivOfRingEquiv
      SevenRealCubic.modelEquivRingOfIntegers
  have hprimField :
      IsPrimitiveRoot (e z) 7 :=
    hprimFrac.map_of_injective e.injective
  have hbound :=
    IsPrimitiveRoot.lcm_totient_le_finrank
      hprimField (IsPrimitiveRoot.one : IsPrimitiveRoot (1 : SevenRealCubic.Field) 1)
      (Polynomial.cyclotomic.irreducible_rat (by norm_num : 0 < Nat.lcm 7 1))
  rw [SevenRealCubic.finrank_eq_three] at hbound
  have hlcm : Nat.lcm 7 1 = 7 := by decide
  have htot : Nat.totient 7 = 6 := by
    rw [Nat.totient_prime (by norm_num : Nat.Prime 7)]
  rw [hlcm, htot] at hbound
  omega

private instance fractionCarrierIrreducibleFact :
    Fact
      (∀ z : RealFrac,
        z ^ 2 ≠
          (-1 : RealFrac) +
            algebraMap SevenRealCubicInt RealFrac (alpha - 1) * z) :=
  ⟨realFrac_quadratic_has_no_root⟩

/-- Coefficientwise extension of the integral quadratic carrier to the real
cubic fraction field. -/
private def toFractionCarrier :
    Ring →+* FractionCarrier where
  toFun x :=
    ⟨algebraMap SevenRealCubicInt RealFrac x.re,
      algebraMap SevenRealCubicInt RealFrac x.im⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_mul' x y := by
    ext <;>
      simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
        map_add, map_mul, map_neg, map_sub, map_one]

private theorem toFractionCarrier_injective :
    Function.Injective toFractionCarrier := by
  intro x y hxy
  apply QuadraticAlgebra.ext
  · apply IsFractionRing.injective SevenRealCubicInt RealFrac
    exact congrArg QuadraticAlgebra.re hxy
  · apply IsFractionRing.injective SevenRealCubicInt RealFrac
    exact congrArg QuadraticAlgebra.im hxy

/-- The concrete rank-six quadratic carrier is an integral domain. This uses
only its injection into the irreducible quadratic extension of the real cubic
fraction field; it does not identify the carrier with a full ring of integers. -/
noncomputable instance ringIsDomain : IsDomain Ring :=
  toFractionCarrier_injective.isDomain toFractionCarrier

#synth IsDomain Ring


end SevenCyclotomicDegreeSixInt

end

end DkMath.FLT.Seven
