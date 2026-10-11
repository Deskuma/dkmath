/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity

#print "file: DkMath.FLT.Seven.GTailFocusedCapacityIndependence"

/-! Actual positive primitive focused non-Fermat witnesses separating support and size. -/

namespace DkMath.FLT.Seven.GTailFocusedCapacityIndependence

open GTailFocusedDefectSquareFirewall GTailFocusedDefectGlobalCapacity

private theorem supportA :
    Nat.primeFactors (13 ^ 2 + 13 * 35 + 35 ^ 2) = {43} := by
  have hp : Nat.Prime 43 := by norm_num
  rw [show 13 ^ 2 + 13 * 35 + 35 ^ 2 = 43 * 43 from by decide,
    Nat.primeFactors_mul (by decide : 43 ≠ 0) (by decide : 43 ≠ 0),
    hp.primeFactors]
  decide

/-- A genuine strict focused countermodel retaining the missing hypothesis. -/
theorem exists_full_support_without_size :
    ∃ a b c g : ℕ,
      (0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧ a + b = c + g ∧
       0 < g ∧ g < a ∧ g < b ∧ a < c ∧ b < c ∧ c < a + b) ∧
      (∀ p ∈ Nat.primeFactors (a ^ 2 + a * b + b ^ 2),
        (p : ℤ) ^ 2 ∣ focusedFermatDefect a b c) ∧
      ¬ ((focusedFermatDefect a b c).natAbs <
        squarePrimeSupportModulus (Nat.primeFactors (a ^ 2 + a * b + b ^ 2))) ∧
      ¬ Fermat7Equation a b c := by
  refine ⟨13, 35, 46, 2, by decide, ?_, ?_, ?_⟩
  · rw [supportA]
    intro p hp
    simp only [Finset.mem_singleton] at hp
    subst p
    decide
  · rw [supportA]
    decide
  · intro h
    exact (by decide : focusedFermatDefect 13 35 46 ≠ 0)
      (focusedFermatDefect_zero_iff.mpr h)

private theorem supportB :
    Nat.primeFactors (1497 ^ 2 + 1497 * 2797 + 2797 ^ 2) = {37, 385171} := by
  have hp : Nat.Prime 37 := by norm_num
  have hr : Nat.Prime 385171 := by norm_num
  rw [show 1497 ^ 2 + 1497 * 2797 + 2797 ^ 2 = 37 * 385171 from by decide,
    Nat.primeFactors_mul (by decide : 37 ≠ 0) (by decide : 385171 ≠ 0),
    hp.primeFactors, hr.primeFactors]
  decide

/-- A genuine strict focused countermodel retaining the missing hypothesis. -/
theorem exists_size_without_full_support :
    ∃ a b c g : ℕ,
      (0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧ a + b = c + g ∧
       0 < g ∧ g < a ∧ g < b ∧ a < c ∧ b < c ∧ c < a + b) ∧
      ((focusedFermatDefect a b c).natAbs <
        squarePrimeSupportModulus (Nat.primeFactors (a ^ 2 + a * b + b ^ 2))) ∧
      ¬ (∀ p ∈ Nat.primeFactors (a ^ 2 + a * b + b ^ 2),
        (p : ℤ) ^ 2 ∣ focusedFermatDefect a b c) ∧
      ¬ Fermat7Equation a b c := by
  refine ⟨1497, 2797, 2802, 1492, by decide, ?_, ?_, ?_⟩
  · rw [supportB]
    decide
  · rw [supportB]
    intro h
    exact (by decide : ¬ (37 : ℤ) ^ 2 ∣ focusedFermatDefect 1497 2797 2802)
      (h 37 (by decide))
  · intro h
    exact (by decide : focusedFermatDefect 1497 2797 2802 ≠ 0)
      (focusedFermatDefect_zero_iff.mpr h)

end DkMath.FLT.Seven.GTailFocusedCapacityIndependence
