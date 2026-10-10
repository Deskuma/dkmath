/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.GTailSevenRealTraceResidue

#print "file: DkMathTest.NumberTheory.GTailSevenRealTraceResidue"

namespace DkMathTest.NumberTheory.GTailSevenRealTraceResidue

open DkMath.Lib.NumberTheory
local instance : Fact (Nat.Prime 43) := ⟨by decide⟩
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

example : (11 : ZMod 43)⁻¹ = 4 := by
  apply inv_eq_of_mul_eq_one_right
  decide
example : seventhRootBeta (11 : ZMod 43) = 16 := by
  have hi : (11 : ZMod 43)⁻¹ = 4 := by
    apply inv_eq_of_mul_eq_one_right
    decide
  rw [seventhRootBeta, hi]
  decide
example : seventhRootBeta (11 : ZMod 43) ^ 3 -
    2 * seventhRootBeta (11 : ZMod 43) ^ 2 - seventhRootBeta (11 : ZMod 43) + 1 = 0 :=
  seventhRootBeta_cubic _ (by decide) (by decide) (by decide)
example : (16 : ZMod 43) ^ 3 - 2 * 16 ^ 2 - 16 + 1 = 0 := by decide
example : seventhRootBeta (1 : ZMod 43) = 3 := by norm_num [seventhRootBeta]
example : (1 : ZMod 43) ^ 7 = 1 ∧
    (3 : ZMod 43) ^ 3 - 2 * 3 ^ 2 - 3 + 1 = 7 ∧ (7 : ZMod 43) ≠ 0 := by decide
example : seventhRootBeta (1 : ZMod 7) ^ 3 -
    2 * seventhRootBeta (1 : ZMod 7) ^ 2 - seventhRootBeta (1 : ZMod 7) + 1 = 0 := by
  norm_num [seventhRootBeta]
  decide
example : ¬ ∃ r : ZMod 7, r ^ 7 = 1 ∧ r ≠ 1 := by decide

#print axioms DkMath.Lib.NumberTheory.seventhRootBeta
#print axioms DkMath.Lib.NumberTheory.seventhRootBeta_cubic
#print axioms DkMath.Lib.NumberTheory.seventhRootBeta_quadratic

end DkMathTest.NumberTheory.GTailSevenRealTraceResidue
