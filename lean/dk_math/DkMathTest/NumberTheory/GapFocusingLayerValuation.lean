/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.GapFocusing.LayerValuation
import DkMath.NumberTheory.GapFocusing.HomogeneousAddress
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand

#print "file: DkMathTest.NumberTheory.GapFocusingLayerValuation"

namespace DkMathTest.GapFocusingLayerValuation

open DkMath.NumberTheory.GapFocusing
open DkMath.CFBRC Polynomial

/-- Distinct cyclotomic indices have the same evaluated integer and prime support. -/
theorem degree_two_six_equal_values :
    DkMath.Lib.NumberTheory.cyclotomicEval 2 (2 : ℤ) = 3 ∧
      DkMath.Lib.NumberTheory.cyclotomicEval 6 (2 : ℤ) = 3 := by
  norm_num [DkMath.Lib.NumberTheory.cyclotomicEval, cyclotomic_two, cyclotomic_six]

/-- The same prime has valuation one in each of the distinct layers `2` and `6`. -/
theorem degree_two_six_equal_prime_load :
    padicValNat 3 (DkMath.Lib.NumberTheory.cyclotomicEval 2 (2 : ℤ)).natAbs = 1 ∧
      padicValNat 3 (DkMath.Lib.NumberTheory.cyclotomicEval 6 (2 : ℤ)).natAbs = 1 := by
  rw [degree_two_six_equal_values.1, degree_two_six_equal_values.2]
  norm_num [padicValNat_self]

/-- The generic first-address bridge recovers the full first-layer valuation. -/
theorem first_order_address_retains_power_difference_load :
    padicValInt 7 (DkMath.Lib.NumberTheory.cyclotomicEval 3 (2 : ℤ)) =
      padicValInt 7 ((2 : ℤ) ^ 3 - 1) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hord : orderOf (2 : ZMod 7) = 3 :=
    orderOf_eq_prime (by decide) (by decide)
  exact padicValInt_cyclotomicEval_eq_pow_sub_one_of_orderOf_eq 2 (by decide)
    (by simpa only [Int.cast_ofNat] using hord) (by norm_num)

/-- The first `2`-layer can carry multiplicity greater than one. -/
theorem first_two_layer_load_two :
    padicValNat 2 (DkMath.Lib.NumberTheory.cyclotomicEval 2 (3 : ℤ)).natAbs = 2 := by
  calc
    _ = padicValNat 2 (3 + 1) := by
      simpa only [Nat.cast_ofNat] using padicValNat_cyclotomicEval_two 3
    _ = 2 := by
      change padicValNat 2 (2 ^ 2) = 2
      exact padicValNat.prime_pow 2

/-- Every later `2`-power layer at the same point has exactly first-order load. -/
theorem later_two_layer_load_one (k : ℕ) :
    padicValNat 2 (DkMath.Lib.NumberTheory.cyclotomicEval (2 ^ (k + 2)) (3 : ℤ)).natAbs = 1 :=
  padicValNat_cyclotomicEval_two_pow_succ_eq_one (by decide) (by decide) (by decide) k

/-- This uses the existing natural-degree homogeneous evaluator directly. -/
theorem homogeneous_degree_three_five_three_eq :
    cyclotomicShiftedEval 3 (2 : ℤ) 3 = 49 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hp : cyclotomic 3 ℤ = X ^ 2 + X + 1 := by
    norm_num [cyclotomic_prime, Finset.sum_range_succ]
    ring
  unfold cyclotomicShiftedEval
  have hd : (cyclotomic 3 ℤ).natDegree = 2 := by
    rw [natDegree_cyclotomic]
    decide
  rw [hd, hp]
  norm_num [Polynomial.homogenize_add, Polynomial.homogenize_X_pow,
    Polynomial.homogenize_X, Polynomial.homogenize_one]

/-- The prime `7` is primitive at degree `3` for the pair `(5,3)`. -/
theorem seven_primitive_degree_three_five_three :
    DkMath.Zsigmondy.PrimitivePrimeDivisor 5 3 3 7 := by
  refine ⟨by decide, by decide, ?_⟩
  intro m hm hlt
  have hmCases : m = 1 ∨ m = 2 := by omega
  rcases hmCases with rfl | rfl <;> decide

/-- The primitive prime's homogeneous layer valuation is two, not one. -/
theorem primitive_homogeneous_layer_load_two :
    DkMath.Zsigmondy.PrimitivePrimeDivisor 5 3 3 7 ∧
      padicValNat 7 (cyclotomicShiftedEval 3 (2 : ℤ) 3).natAbs = 2 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  refine ⟨seven_primitive_degree_three_five_three, ?_⟩
  rw [homogeneous_degree_three_five_three_eq]
  change padicValNat 7 (7 ^ 2) = 2
  exact padicValNat.prime_pow 2

#print axioms padicValNat_pow_sub_pow_mul_prime_pow
#print axioms padicValInt_cyclotomicEval_eq_pow_sub_one_of_orderOf_eq
#print axioms padicValNat_pow_sub_pow_mul_two_pow_succ
#print axioms natAbs_cyclotomicEval_prime_pow
#print axioms natAbs_cyclotomicEval_prime_pow_mul_sub_one
#print axioms padicValNat_cyclotomicEval_prime_pow_eq_one
#print axioms padicValNat_cyclotomicEval_two
#print axioms padicValNat_cyclotomicEval_two_pow_succ_eq_one
#print axioms degree_two_six_equal_values
#print axioms degree_two_six_equal_prime_load
#print axioms first_order_address_retains_power_difference_load
#print axioms first_two_layer_load_two
#print axioms later_two_layer_load_one
#print axioms homogeneous_degree_three_five_three_eq
#print axioms seven_primitive_degree_three_five_three
#print axioms primitive_homogeneous_layer_load_two

end DkMathTest.GapFocusingLayerValuation
