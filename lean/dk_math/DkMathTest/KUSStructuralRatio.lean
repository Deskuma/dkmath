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

example {ε : ℝ} (hε : 0 < ε) :
    regularizedSelfRatio 0 ε = 1 := by
  exact regularizedZeroSelfRatio_eq_one hε

end DkMathTest.KUSStructuralRatio
