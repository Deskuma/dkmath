/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.MazurStepThreeTwoAnchor
import Mathlib.Algebra.Field.ZMod

namespace DkMathTest.Lib.Algebra.MazurStepThreeTwoAnchor

open DkMath.Lib.Algebra.MazurStepThreeTwoAnchor

-- The zero specialization of Z/8 has a nontrivial 2-primary kernel.
-- Prime-to-2 injectivity still holds; full injectivity is deliberately absent.
example : ∃ a : ℕ, 2 ^ a • (1 : ZMod 8) = 0 := by
  apply exists_prime_power_nsmul_eq_zero_of_specialization_zero
    (⊤ : AddSubgroup (ZMod 8)) Nat.prime_two (0 : ZMod 8 →+ ZMod 3)
  · intro z _ htor _
    obtain ⟨m, hm, hmz⟩ := htor
    have hcop : m.Coprime 8 := by
      change m.Coprime (2 ^ 3)
      simpa only [pow_one] using ((Nat.prime_two.coprime_iff_not_dvd.mpr hm).symm.pow 1 3)
    exact eq_zero_of_coprime_nsmul hcop hmz (by
      have hall : ∀ x : ZMod 8, 8 • x = 0 := by decide
      exact hall z)
  · trivial
  · rfl

-- Coprimality cannot be removed: two powers of the same prime kill a
-- nonzero element, so using the same anchor twice would give a false theorem.
example : ∃ z : ZMod 2, z ≠ 0 ∧ 2 • z = 0 ∧ 4 • z = 0 := by
  exact ⟨1, by decide, by decide, by decide⟩

#print axioms exists_prime_power_nsmul_eq_zero_of_specialization_zero
#print axioms eq_zero_of_two_three_specializations
#print axioms nonzero_cusp_not_killed_after_two_anchors

end DkMathTest.Lib.Algebra.MazurStepThreeTwoAnchor
