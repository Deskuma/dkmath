/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.KUS.StructuralRatio

#print "file: DkMathTest.KUSStructuralRatio"

namespace DkMathTest.KUSStructuralRatio

open DkMath.KUS

example {R : Type*} [MonoidWithZero R] :
    (0 : R) ^ (0 : ℕ) = 1 := by
  exact zero_pow_zero_eq_one

example {R : Type*} [MonoidWithZero R] :
    (0 : R) ^ (1 : ℕ) = 0 := by
  exact zero_pow_one_eq_zero

example (n : ℕ) :
    exponentQuotient (0 : ℝ) n n = 1 := by
  exact zero_exponentQuotient_self n

example :
    (StructuralRatioWitness.self (0 : ℝ)).value = 1 := by
  simp

example {x : ℝ} (hx : x ≠ 0) :
    (StructuralRatioWitness.self x).value = x / x := by
  exact
    StructuralRatioWitness.value_eq_div_of_denominator_ne
      (StructuralRatioWitness.self x) hx

example {x y : ℝ} (hy : y ≠ 0) :
    (DefinedRatioWitness.of_denominator_ne
      (numerator := x) (denominator := y) hy).value = x / y := by
  simp

example {x y : ℝ} :
    DefinedRatioWitness ℝ x y ↔ y ≠ 0 := by
  exact DefinedRatioWitness.defined_iff_denominator_ne x y

example {x : ℝ} :
    ¬ DefinedRatioWitness ℝ x 0 := by
  exact DefinedRatioWitness.not_defined_of_denominator_eq_zero x 0 rfl

example {x ε : ℝ} (hε : ε ≠ -x) :
    regularizedSelfRatio x ε = 1 := by
  exact regularizedSelfRatio_eq_one_of_offset_ne_neg hε

example (x : ℝ) :
    Filter.Tendsto
      (fun ε : ℝ => regularizedSelfRatio x ε)
      (nhdsWithin (-x) ({-x}ᶜ : Set ℝ))
      (nhds 1) := by
  exact tendsto_regularizedSelfRatio_punctured x

example (x : ℝ) :
    Filter.Tendsto
      (fun ε : ℝ => regularizedSelfRatio x ε)
      (nhdsWithin (-x) (Set.Ioi (-x)))
      (nhds 1) := by
  exact tendsto_regularizedSelfRatio_right x

example {ε : ℝ} (hε : 0 < ε) :
    regularizedSelfRatio 0 ε = 1 := by
  exact regularizedZeroSelfRatio_eq_one hε

example :
    Filter.Tendsto
      (fun ε : ℝ => regularizedSelfRatio 0 ε)
      (nhdsWithin 0 ({0}ᶜ : Set ℝ))
      (nhds 1) := by
  exact tendsto_regularizedZeroSelfRatio_punctured

example :
    Filter.Tendsto
      (fun ε : ℝ => regularizedSelfRatio 0 ε)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 1) := by
  exact tendsto_regularizedZeroSelfRatio_right

end DkMathTest.KUSStructuralRatio
