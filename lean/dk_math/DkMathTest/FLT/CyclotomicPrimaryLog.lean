/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.CyclotomicPrimaryLogCriterion

#print "file: DkMathTest.FLT.CyclotomicPrimaryLog"

namespace DkMathTest.FLT.CyclotomicPrimaryLog

open DkMath.Lib.NumberTheory DkMath.Lib.Algebra
open CyclotomicPrimaryUnitSpace CyclotomicPrimaryCongruence KummerSelmerExact
open CyclotomicTruncatedLog CyclotomicPrimaryLog CyclotomicPrimaryLogCriterion
open IsCyclotomicExtension
open scoped NumberField
set_option backward.isDefEq.respectTransparency false
noncomputable section

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev F := CyclotomicField 5 ℚ
private theorem hζ : IsPrimitiveRoot (zeta 5 ℚ F) 5 := zeta_spec 5 ℚ F

-- Actual residue cardinality and ramification, in the actual fifth cyclotomic number field.
example : Nat.card (NumberField.RingOfIntegers F ⧸ (ramifiedPlace hζ).asIdeal) = 5 :=
  ramified_residue_card hζ

example : (5 : NumberField.RingOfIntegers F) ∈ ramifiedIdeal hζ ^ 4 :=
  natCast_mem_ramifiedIdeal_pow hζ 4 (by decide)

-- The cubic quotient is meaningful: lambda^2 does not vanish modulo lambda^3.
example : (hζ.toInteger - 1) ^ 2 ∉ ramifiedIdeal hζ ^ 3 := by
  rw [ramifiedIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    pow_dvd_pow_iff hζ.zeta_sub_one_prime'.ne_zero hζ.zeta_sub_one_prime'.not_isUnit]
  omega

private def c : (NumberField.RingOfIntegers F)ˣ :=
  (hζ.toInteger_isPrimitiveRoot.geom_sum_isUnit (by decide : 2 ≤ 5)
    (by decide : Nat.Coprime 2 5)).unit

-- The chosen cyclotomic unit has the actual value 1+zeta.
example : (c : NumberField.RingOfIntegers F) = 1 + hζ.toInteger := by
  simpa only [c, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one]
    using (hζ.toInteger_isPrimitiveRoot.geom_sum_isUnit (by decide : 2 ≤ 5)
      (by decide : Nat.Coprime 2 5)).unit_spec

private theorem fifth_power_local :
    Additive.ofMul ((c ^ 5 : (NumberField.RingOfIntegers F)ˣ) :
      UnitClass (NumberField.RingOfIntegers F) 5) ∈ localPowerSpace F 5 := by
  have hclass : ((c ^ 5 : (NumberField.RingOfIntegers F)ˣ) :
      UnitClass (NumberField.RingOfIntegers F) 5) = 1 :=
    (QuotientGroup.eq_one_iff (c ^ 5)).mpr ⟨c, rfl⟩
  rw [hclass]
  exact (localPowerSpace F 5).zero_mem


-- Actual characteristic and inverse of 2, derived without new arithmetic inputs.
example : (5 : ResidueCube hζ) = 0 := natCast_eq_zero hζ (by decide)
example : 2 * half hζ (by decide) = 1 := two_mul_half hζ (by decide)

-- The uncorrected z−1 is not additive on 1+(lambda); the quadratic correction matters.
example : ((1 + parameter hζ) * (1 + parameter hζ) - 1) ≠
    ((1 + parameter hζ) - 1) + ((1 + parameter hζ) - 1) := by
  intro he
  apply parameter_sq_ne_zero hζ
  calc
    parameter hζ ^ 2 = ((1 + parameter hζ) * (1 + parameter hζ) - 1) -
      (((1 + parameter hζ) - 1) + ((1 + parameter hζ) - 1)) := by ring
    _ = 0 := sub_eq_zero.mpr he

-- The corrected logarithm is additive for the same actual parameter.
example : tlog (half hζ (by decide)) ((1 + parameter hζ) * (1 + parameter hζ)) =
    tlog (half hζ (by decide)) (1 + parameter hζ) +
      tlog (half hζ (by decide)) (1 + parameter hζ) := by
  apply tlog_mul (parameterIdeal_cube hζ) (two_mul_half hζ (by decide)) <;>
    rw [add_sub_cancel_left] <;> exact Ideal.mem_span_singleton_self _

-- Truncated log detects lambda² in Q. This does not claim a global omega² unit generator.
example : tlog (half hζ (by decide)) (1 + parameter hζ ^ 2) = parameter hζ ^ 2 := by
  have h4 : parameter hζ ^ 4 = 0 := by
    calc
      parameter hζ ^ 4 = parameter hζ ^ 3 * parameter hζ := pow_succ _ 3
      _ = 0 := by rw [parameter_cube, zero_mul]
  simp only [tlog, add_sub_cancel_left, ← pow_mul, show (2 : ℕ) * 2 = 4 from rfl, h4,
    mul_zero, sub_zero]

-- A genuine global fifth power has zero class and zero logarithm.
example : primaryLog hζ (by decide) (Additive.ofMul
    ((c ^ 5 : (NumberField.RingOfIntegers F)ˣ) : UnitClass (NumberField.RingOfIntegers F) 5)) = 0 :=
  primaryLog_mk_eq_zero_of_local_power hζ (by decide) (c ^ 5) fifth_power_local

-- Multiplying a representative by an actual fifth power does not change Lambda.
example (u v : (NumberField.RingOfIntegers F)ˣ) :
    unitLog hζ (by decide) (Additive.ofMul (u * v ^ 5)) =
      unitLog hζ (by decide) (Additive.ofMul u) := by
  rw [ofMul_mul, map_add, unitLog_pow, add_zero]

#print axioms tlog_mul
#print axioms parameter_sq_ne_zero
#print axioms residueCharP
#print axioms unitLog_pow
#print axioms primaryLog
#print axioms primaryLog_mk_eq_zero_of_local_power
#print axioms primaryLog_eq_zero_of_mem_localPowerSpace
#print axioms primaryLog_smul
#print axioms eq_zero_of_rank_one_of_log_eq_zero
#print axioms primaryWeightSquareSpace_eq_bot_of_rank_one_of_detection

end
end DkMathTest.FLT.CyclotomicPrimaryLog
