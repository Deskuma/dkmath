/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailCyclotomicTailSecondDigit

#print "file: DkMathTest.FLT.Seven.GTailCyclotomicTailSecondDigit"

namespace DkMathTest.FLT.Seven.GTailCyclotomicTailSecondDigit

open DkMath.FLT.Seven DkMath.Lib.NumberTheory DkMath.CosmicFormula Polynomial

local instance : Fact (Nat.Prime 43) := ⟨by decide⟩
local notation "K" => sixRootKernel (11 : ZMod 43) (by decide) (by decide) (by decide)

private theorem ratio1165 : gtailSevenTailRatio 43 9 1165 = 11 := by
  dsimp [gtailSevenTailRatio]
  apply (div_eq_iff (by decide : (9 : ZMod 43) ≠ 0)).mpr
  decide

private theorem derivative28 :
    (tailShellPoly ((9 : ℕ) : ZMod 43)).derivative.eval ((9 + 1165 : ℕ) : ZMod 43) = 28 := by
  have h := gtail_shell_derivative_formula (q := 43) 9 1165 (by decide) (by decide)
  have hv : (7 : ZMod 43) * 1174 ^ 6 / 1165 = 28 := by
    apply (div_eq_iff (by decide : (1165 : ZMod 43) ≠ 0)).mpr
    decide
  exact h.trans hv

private theorem lift17 : (43 : ℕ) ^ 3 ∣ GTail 7 1 (1165 + 43 ^ 2 * 17) 9 := by
  apply (gtail_second_lift_iff_linear (q := 43) 9 1165 17 (by decide)).mpr
  rw [derivative28]
  decide

private theorem digit_unique (d : Fin 43)
    (hd : (43 : ℕ) ^ 3 ∣ GTail 7 1 (1165 + 43 ^ 2 * d.val) 9) : d = 17 := by
  obtain ⟨t, ht, hu⟩ := existsUnique_gtail_second_digit (q := 43) 9 1165
    (by decide) (by decide) (by decide)
  exact (hu d hd).trans (hu 17 lift17).symm

example (q c g d : ℕ) :
    (tailShellPoly (c : ℤ)).eval (((c + g : ℕ) : ℤ) + (q : ℤ) ^ 2 * (d : ℤ)) =
      ((GTail 7 1 (g + q ^ 2 * d) c : ℕ) : ℤ) := gtail_second_shift_eval _ _ _ _
example (c g d : ℕ) :
    (tailShellPoly (c : ℤ)).eval (((c + g : ℕ) : ℤ) + (0 : ℤ) ^ 2 * (d : ℤ)) =
      ((GTail 7 1 (g + 0 ^ 2 * d) c : ℕ) : ℤ) := gtail_second_shift_eval _ _ _ _
example (q g d : ℕ) :
    (tailShellPoly (0 : ℤ)).eval (((0 + g : ℕ) : ℤ) + (q : ℤ) ^ 2 * (d : ℤ)) =
      ((GTail 7 1 (g + q ^ 2 * d) 0 : ℕ) : ℤ) := gtail_second_shift_eval _ _ _ _
example (q c d : ℕ) :
    (tailShellPoly (c : ℤ)).eval (((c + 0 : ℕ) : ℤ) + (q : ℤ) ^ 2 * (d : ℤ)) =
      ((GTail 7 1 (0 + q ^ 2 * d) c : ℕ) : ℤ) := gtail_second_shift_eval _ _ _ _
example : GTail 7 1 (1165 : ℕ) 9 = 2638461449052811747 := by decide
example : (43 : ℕ) ^ 2 ∣ GTail 7 1 1165 9 := by decide
example : ((GTail 7 1 1165 9 / 43 ^ 2 : ℕ) : ZMod 43) = 40 := by decide
example : (tailShellPoly (9 : ZMod 43)).derivative.eval 1174 = 28 := derivative28
example : (40 : ZMod 43) + 17 * 28 = 0 := by decide
example : (1165 : ℕ) + 43 ^ 2 * 17 = 32598 := by decide
example : ∃! t : Fin 43, (43 : ℕ) ^ 3 ∣ GTail 7 1 (1165 + 43 ^ 2 * t.val) 9 :=
  existsUnique_gtail_second_digit _ _ (by decide) (by decide) (by decide)
example : (43 : ℕ) ^ 3 ∣ GTail 7 1 32598 9 := lift17
example : ∀ d : Fin 43, (43 : ℕ) ^ 3 ∣ GTail 7 1 (1165 + 43 ^ 2 * d.val) 9 ↔ d = 17 := by
  intro d
  constructor
  · exact digit_unique d
  · intro hd
    rw [hd]
    exact lift17
example : ¬ (43 : ℕ) ^ 3 ∣ GTail 7 1 (1165 + 43 ^ 2 * 16) 9 := by
  intro hd
  have h := digit_unique 16 hd
  exact (by decide : (16 : Fin 43) ≠ 17) h
example : ¬ (43 : ℕ) ^ 3 ∣ GTail 7 1 1165 9 := by
  intro hd
  have h := digit_unique 0 hd
  exact (by decide : (0 : Fin 43) ≠ 17) h
example : ∀ d : ℕ, (43 : ℕ) ^ 3 ∣ GTail 7 1 (1165 + 43 ^ 2 * d) 9 ↔
    (d : ZMod 43) = 17 := by
  intro d
  rw [gtail_second_lift_iff_linear 9 1165 d (by decide), derivative28]
  have hm : ((GTail 7 1 1165 9 / 43 ^ 2 : ℕ) : ZMod 43) = 40 := by decide
  rw [hm]
  constructor
  · intro hd
    apply mul_right_cancel₀ (by decide : (28 : ZMod 43) ≠ 0)
    have he : (40 : ZMod 43) + 17 * 28 = 0 := by decide
    linear_combination hd - he
  · intro hd
    rw [hd]
    decide
example : (43 : ℕ) ^ 3 ∣ GTail 7 1 (1165 + 43 ^ 2 * 60) 9 := by
  rw [gtail_second_lift_iff_linear 9 1165 60 (by decide), derivative28]
  decide
example : ¬ (43 : ℕ) ^ 4 ∣ GTail 7 1 32598 9 := by decide
example : ¬ (43 : ℕ) ∣ 32598 :=
  gtail_second_shift_gap_unit 1165 17 (by decide)
example : gtailSevenTailRatio 43 9 32598 = 11 := by
  exact (gtail_second_shift_ratio (q := 43) 9 1165 17).trans ratio1165
example : (tailShellPoly (9 : ZMod 43)).derivative.eval 32607 = 28 := by
  have hs := gtail_second_shift_derivative (q := 43) 9 1165 17
  exact hs.trans derivative28
example : ∀ i : Fin 6, gtailCyclotomicFactor 9 32598 i ∈ K (sixInverseSlot i) ^ 2 := by
  intro i
  have ht2 : (43 : ℕ) ^ 2 ∣ GTail 7 1 32598 9 :=
    (by decide : (43 : ℕ) ^ 2 ∣ 43 ^ 3).trans lift17
  have ht : (43 : ℕ) ∣ GTail 7 1 32598 9 := gtail_support_of_square _ _ ht2
  have hg : ¬ (43 : ℕ) ∣ 32598 := gtail_second_shift_gap_unit 1165 17 (by decide)
  have h := gtailCyclotomicFactor_mem_square_of_sq_dvd_GTail 9 32598 (by decide) hg ht ht2 i
  have hr : gtailSevenTailRatio 43 9 32598 = 11 :=
    (gtail_second_shift_ratio 9 1165 17).trans ratio1165
  simpa only [hr] using h
example : gtailFirstCorrection (q := 43) 9 4 = 27 := by
  apply (gtailFirstCorrection_unique 9 4 (by decide) (by decide) (by decide) 27 _).symm
  have hv := gtail_shell_derivative_formula (q := 43) 9 4 (by decide) (by decide)
  have hd : (tailShellPoly ((9 : ℕ) : ZMod 43)).derivative.eval ((9 + 4 : ℕ) : ZMod 43) = 28 := by
    have he : (7 : ZMod 43) * 13 ^ 6 / 4 = 28 := by
      apply (div_eq_iff (by decide : (4 : ZMod 43) ≠ 0)).mpr
      decide
    exact hv.trans he
  rw [hd]
  decide
example : (43 : ℕ) ^ 2 ∣ GTail 7 1 (4 + 43 * 27) 9 := by
  apply (gtail_lift_sq_iff_linear 9 4 27 (by decide)).mpr
  have hd : (tailShellPoly ((9 : ℕ) : ZMod 43)).derivative.eval ((9 + 4 : ℕ) : ZMod 43) = 28 := by
    have h := gtail_shell_derivative_formula (q := 43) 9 4 (by decide) (by decide)
    have he : (7 : ZMod 43) * 13 ^ 6 / 4 = 28 := by
      apply (div_eq_iff (by decide : (4 : ZMod 43) ≠ 0)).mpr
      decide
    exact h.trans he
  rw [hd]
  decide
example : ¬ ∃ r : ZMod 7, r ^ 7 = 1 ∧ r ≠ 1 := by decide
example : ¬ (13 : ℕ) ∣ GTail 7 1 13 30 := by decide
example : (43 : ℕ) ∣ 0 := by decide
example : ¬ Fermat7Equation 5 8 9 := by unfold Fermat7Equation; decide

#print axioms DkMath.FLT.Seven.gtail_second_shift_eval
#print axioms DkMath.FLT.Seven.gtail_support_of_square
#print axioms DkMath.FLT.Seven.gtail_integer_square_support
#print axioms DkMath.FLT.Seven.gtail_integer_derivative_not_dvd
#print axioms DkMath.FLT.Seven.gtail_second_lift_predicate
#print axioms DkMath.FLT.Seven.existsUnique_gtail_second_digit
#print axioms DkMath.FLT.Seven.gtail_second_lift_iff_linear
#print axioms DkMath.FLT.Seven.gtail_second_shift_gap_unit
#print axioms DkMath.FLT.Seven.gtail_second_shift_ratio
#print axioms DkMath.FLT.Seven.gtail_second_shift_derivative

end DkMathTest.FLT.Seven.GTailCyclotomicTailSecondDigit
