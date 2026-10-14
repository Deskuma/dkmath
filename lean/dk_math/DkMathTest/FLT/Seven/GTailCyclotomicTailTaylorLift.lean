/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailCyclotomicTailTaylorLift

#print "file: DkMathTest.FLT.Seven.GTailCyclotomicTailTaylorLift"

namespace DkMathTest.FLT.Seven.GTailCyclotomicTailTaylorLift

open DkMath.FLT.Seven DkMath.CosmicFormula DkMath.Lib.NumberTheory Polynomial

local instance : Fact (Nat.Prime 43) := ⟨by decide⟩

private theorem derivative28 :
    (tailShellPoly (9 : ZMod 43)).derivative.eval 13 = 28 := by
  have h := gtail_shell_derivative_formula (q := 43) 9 4 (by decide) (by decide)
  have hv : (7 : ZMod 43) * 13 ^ 6 / 4 = 28 := by
    apply (div_eq_iff (by decide : (4 : ZMod 43) ≠ 0)).mpr
    decide
  exact h.trans hv

private theorem correction27 : gtailFirstCorrection (q := 43) 9 4 = 27 := by
  apply (gtailFirstCorrection_unique (q := 43) 9 4
    (by decide) (by decide) (by decide) 27 _).symm
  have hv : (tailShellPoly ((9 : ℕ) : ZMod 43)).derivative.eval ((9 + 4 : ℕ) : ZMod 43) = 28 := by
    exact derivative28
  rw [hv]
  decide

example (q c g d : ℕ) :
    (q : ℤ) ^ 2 ∣ ((GTail 7 1 (g + q * d) c : ℕ) : ℤ) -
      ((GTail 7 1 g c : ℕ) : ℤ) - ((q * d : ℕ) : ℤ) * gtailDerivativeInt c g :=
  gtail_integer_taylor _ _ _ _
example (q c g : ℕ) :
    (q : ℤ) ^ 2 ∣ ((GTail 7 1 (g + q * 0) c : ℕ) : ℤ) -
      ((GTail 7 1 g c : ℕ) : ℤ) - ((q * 0 : ℕ) : ℤ) * gtailDerivativeInt c g :=
  gtail_integer_taylor _ _ _ _
example (c g d : ℕ) :
    (0 : ℤ) ^ 2 ∣ ((GTail 7 1 (g + 0 * d) c : ℕ) : ℤ) -
      ((GTail 7 1 g c : ℕ) : ℤ) - ((0 * d : ℕ) : ℤ) * gtailDerivativeInt c g :=
  gtail_integer_taylor _ _ _ _
example (q g d : ℕ) :
    (q : ℤ) ^ 2 ∣ ((GTail 7 1 (g + q * d) 0 : ℕ) : ℤ) -
      ((GTail 7 1 g 0 : ℕ) : ℤ) - ((q * d : ℕ) : ℤ) * gtailDerivativeInt 0 g :=
  gtail_integer_taylor _ _ _ _
example (q c d : ℕ) :
    (q : ℤ) ^ 2 ∣ ((GTail 7 1 (0 + q * d) c : ℕ) : ℤ) -
      ((GTail 7 1 0 c : ℕ) : ℤ) - ((q * d : ℕ) : ℤ) * gtailDerivativeInt c 0 :=
  gtail_integer_taylor _ _ _ _
example : (3 : ℤ) ^ 2 ∣ (tailShellPoly (-2 : ℤ)).eval (-5 + 3) -
    (tailShellPoly (-2 : ℤ)).eval (-5) - 3 * (tailShellPoly (-2 : ℤ)).derivative.eval (-5) :=
  tailShellPoly_integer_taylor _ _ _
example : GTail 7 1 (4 : ℕ) 9 = 14491387 := by decide
example : (43 : ℕ) ∣ GTail 7 1 4 9 ∧ ¬ (43 : ℕ) ^ 2 ∣ GTail 7 1 4 9 := by decide
example : ((GTail 7 1 4 9 / 43 : ℕ) : ZMod 43) = 18 := by decide
example : (tailShellPoly (9 : ZMod 43)).derivative.eval 13 = 28 := derivative28
example : (18 : ZMod 43) + 27 * 28 = 0 := by decide
example : gtailFirstCorrection (q := 43) 9 4 = 27 := correction27
example : (gtailFirstCorrection (q := 43) 9 4).val = 27 := by
  rw [correction27]
  decide
example : (4 : ℕ) + 43 * 27 = 1165 := by decide
example : (43 : ℕ) ^ 2 ∣ GTail 7 1 1165 9 := by
  apply (gtail_lift_sq_iff_correction (q := 43) 9 4 27
    (by decide) (by decide) (by decide)).mpr
  exact correction27.symm
example : ∀ d : ℕ, (43 : ℕ) ^ 2 ∣ GTail 7 1 (4 + 43 * d) 9 ↔
    (d : ZMod 43) = 27 := by
  intro d
  rw [gtail_lift_sq_iff_correction 9 4 d (by decide) (by decide) (by decide), correction27]
example : ¬ (43 : ℕ) ^ 2 ∣ GTail 7 1 (4 + 43 * 0) 9 := by
  rw [gtail_lift_sq_iff_correction 9 4 0 (by decide) (by decide) (by decide), correction27]
  decide
example : ¬ (43 : ℕ) ^ 2 ∣ GTail 7 1 (4 + 43 * 26) 9 := by
  rw [gtail_lift_sq_iff_correction 9 4 26 (by decide) (by decide) (by decide), correction27]
  decide
example : (43 : ℕ) ^ 2 ∣ GTail 7 1 (4 + 43 * 70) 9 := by
  rw [gtail_lift_sq_iff_correction 9 4 70 (by decide) (by decide) (by decide), correction27]
  decide
example : ¬ (43 : ℕ) ∣ 9 ∧ ¬ (43 : ℕ) ∣ 1165 := by decide
example : gtailSevenTailRatio 43 9 1165 = gtailSevenTailRatio 43 9 4 :=
  gtail_shift_ratio 9 4 27
example : gtailSevenTailRatio 43 9 1165 = 11 := by
  rw [gtail_shift_ratio (q := 43) 9 4 27]
  dsimp [gtailSevenTailRatio]
  apply (div_eq_iff (by decide : (9 : ZMod 43) ≠ 0)).mpr
  decide
example : (tailShellPoly (9 : ZMod 43)).derivative.eval 1174 = 28 := by
  have hs := gtail_shift_derivative (q := 43) 9 4 27
  have he : (tailShellPoly (9 : ZMod 43)).derivative.eval 1174 =
      (tailShellPoly (9 : ZMod 43)).derivative.eval 13 := by
    exact hs
  exact he.trans derivative28
example : ∀ i : Fin 6, gtailCyclotomicFactor 9 1165 i ∈
    sixRootKernel (gtailSevenTailRatio 43 9 1165)
      (gtailSevenTailRatio_ne_zero (by decide) (by decide))
      (gtailSevenTailRatio_pow_seven (by decide) (by decide))
      (gtailSevenTailRatio_ne_one (by decide) (by decide)) (sixInverseSlot i) ^ 2 := by
  intro i
  have hl : (43 : ℕ) ^ 2 ∣ GTail 7 1 1165 9 :=
    (gtail_lift_sq_iff_correction (q := 43) 9 4 27
      (by decide) (by decide) (by decide)).mpr correction27.symm
  exact gtailCyclotomicFactor_mem_square_of_sq_dvd_GTail 9 1165
    (by decide) (by decide) (by decide) hl i
example : ¬ Fermat7Equation 5 8 9 := by unfold Fermat7Equation; decide

#print axioms DkMath.FLT.Seven.gtailDerivativeInt
#print axioms DkMath.FLT.Seven.tailShellPoly_integer_taylor
#print axioms DkMath.FLT.Seven.gtail_integer_taylor
#print axioms DkMath.FLT.Seven.gtailDerivativeInt_cast
#print axioms DkMath.FLT.Seven.gtail_lift_sq_iff_linear
#print axioms DkMath.FLT.Seven.gtailFirstCorrection
#print axioms DkMath.FLT.Seven.gtail_shell_derivative_ne_zero
#print axioms DkMath.FLT.Seven.gtailFirstCorrection_equation
#print axioms DkMath.FLT.Seven.gtailFirstCorrection_unique
#print axioms DkMath.FLT.Seven.gtail_lift_sq_iff_correction
#print axioms DkMath.FLT.Seven.gtail_first_correction_lifts
#print axioms DkMath.FLT.Seven.gtail_shift_cast
#print axioms DkMath.FLT.Seven.gtail_shift_gap_unit
#print axioms DkMath.FLT.Seven.gtail_shift_ratio
#print axioms DkMath.FLT.Seven.gtail_shift_derivative
#print axioms DkMath.FLT.Seven.gtail_shift_tail_support

end DkMathTest.FLT.Seven.GTailCyclotomicTailTaylorLift
