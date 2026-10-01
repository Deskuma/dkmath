/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Gauge

#print "file: DkMathTest.NumberTheory.Gauge.Value"

namespace DkMathTest.NumberTheory.Gauge

open DkMath.NumberTheory.Gauge

#check ValueGaugePrime
#check valueGaugeResidue
#check valueGaugeCoordinates
#check valueGaugeResidue_eq_mod
#check valueGaugeCoordinates_apply
#check valueGaugeResidue_pow_eq_zero
#check valueGaugeCoordinates_pow_eq_zero
#check valueGaugeCoordinates_mul_pow
#check ValueGaugePure
#check valueGaugePure_pow
#check not_valueGaugePure_zero

example : ValueGaugePure 2 36 := by
  have h := valueGaugePure_pow (n := 2) (a := 6) (by norm_num)
  norm_num at h
  exact h

example : ¬ ValueGaugePure 2 72 := by
  intro h
  have hcoord := congrFun h.2 (⟨2, by norm_num⟩ : ValueGaugePrime)
  change valueGaugeResidue 2 (⟨2, by norm_num⟩ : ValueGaugePrime) 72 = 0 at hcoord
  have hv : padicValNat 2 72 = 3 := by
    calc
      padicValNat 2 72 = padicValNat 2 (9 * 2 ^ 3) := by norm_num
      _ = padicValNat 2 9 + 3 * padicValNat 2 2 := by
        exact DkMath.NumberTheory.StructuralArithmetic.padicValNat_mul_pow
          (p := 2) (n := 9) (a := 2) (d := 3)
          (by norm_num) (by norm_num) (by norm_num)
      _ = 3 := by norm_num [padicValNat.eq_zero_iff]
  rw [valueGaugeResidue_eq_mod, hv] at hcoord
  norm_num at hcoord

example : ValueGaugePure 3 27 := by
  have h := valueGaugePure_pow (n := 3) (a := 3) (by norm_num)
  norm_num at h
  exact h

example :
    valueGaugeCoordinates 3 (7 * 5 ^ 3) = valueGaugeCoordinates 3 7 := by
  exact valueGaugeCoordinates_mul_pow (n := 3) (a := 7) (b := 5)
    (by norm_num) (by norm_num)

example (p : ValueGaugePrime) (a : ℕ) :
    valueGaugeResidue 0 p a = padicValNat p.1 a := by
  exact valueGaugeResidue_period_zero p a

example (p : ValueGaugePrime) (a : ℕ) :
    valueGaugeResidue 1 p a = 0 := by
  exact valueGaugeResidue_period_one p a

example : ValueGaugePure 0 1 := by
  exact valueGaugePure_pow (n := 0) (a := 1) (by norm_num)

example : ValueGaugePure 1 1 := by
  exact valueGaugePure_pow (n := 1) (a := 1) (by norm_num)

example : ¬ ValueGaugePure 2 0 := by
  exact not_valueGaugePure_zero 2

end DkMathTest.NumberTheory.Gauge
