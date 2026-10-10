/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailCyclotomicTailDerivative

#print "file: DkMathTest.FLT.Seven.GTailCyclotomicTailDerivative"

namespace DkMathTest.FLT.Seven.GTailCyclotomicTailDerivative

open DkMath.FLT.Seven DkMath.Lib.NumberTheory DkMath.CosmicFormula Polynomial
open SevenCyclotomicDegreeSixInt

local instance : Fact (Nat.Prime 43) := ⟨by decide⟩
local instance : Fact (Nat.Prime 13) := ⟨by decide⟩
local notation "K" => sixRootKernel (11 : ZMod 43) (by decide) (by decide) (by decide)

private theorem ratio4 : gtailSevenTailRatio 43 9 4 = 11 := by
  dsimp [gtailSevenTailRatio]
  apply (div_eq_iff (by decide : (9 : ZMod 43) ≠ 0)).mpr
  decide
private theorem ratio1165 : gtailSevenTailRatio 43 9 1165 = 11 := by
  dsimp [gtailSevenTailRatio]
  apply (div_eq_iff (by decide : (9 : ZMod 43) ≠ 0)).mpr
  decide

example {A : Type*} [CommRing A] (c : A) :
    (X - C c) * tailShellPoly c = X ^ 7 - C (c ^ 7) := tailShellPoly_mul c
example {A : Type*} [CommRing A] (c : A) :
    tailShellPoly c + (X - C c) * (tailShellPoly c).derivative = 7 * X ^ 6 :=
  tailShellPoly_derivative_identity c
example {A : Type*} [CommRing A] (c g : ℕ) :
    (tailShellPoly (c : A)).eval ((c + g : ℕ) : A) = ((GTail 7 1 g c : ℕ) : A) :=
  tailShellPoly_eval_nat _ _

example : GTail 7 1 (4 : ℕ) 9 = 14491387 := by decide
example : GTail 7 1 (1165 : ℕ) 9 = 2638461449052811747 := by decide
example : (43 : ℕ) ∣ GTail 7 1 (4 : ℕ) 9 ∧
    ¬ (43 : ℕ) ^ 2 ∣ GTail 7 1 (4 : ℕ) 9 := by decide
example : (43 : ℕ) ^ 2 ∣ GTail 7 1 (1165 : ℕ) 9 := by decide
example : (1165 : ZMod 43) = 4 ∧ (1174 : ZMod 43) = 13 := by decide
example : (7 : ZMod 43) * 13 ^ 6 / 4 = 28 := by
  apply (div_eq_iff (by decide : (4 : ZMod 43) ≠ 0)).mpr
  decide

-- Both derivative values are obtained from the generic formal derivative identity.
example : (tailShellPoly (9 : ZMod 43)).derivative.eval 13 = 28 := by
  have h := gtail_shell_derivative_formula (q := 43) 9 4 (by decide) (by decide)
  have hv : (7 : ZMod 43) * 13 ^ 6 / 4 = 28 := by
    apply (div_eq_iff (by decide : (4 : ZMod 43) ≠ 0)).mpr
    decide
  simpa using h.trans hv
example : (tailShellPoly (9 : ZMod 43)).derivative.eval 1174 = 28 := by
  have h := gtail_shell_derivative_formula (q := 43) 9 1165 (by decide) (by decide)
  have hv : (7 : ZMod 43) * 1174 ^ 6 / 1165 = 28 := by
    apply (div_eq_iff (by decide : (1165 : ZMod 43) ≠ 0)).mpr
    decide
  simpa using h.trans hv
example : (tailShellPoly (9 : ZMod 43)).eval 13 = 0 := by
  have h := tailShellPoly_eval_nat (A := ZMod 43) 9 4
  have hz : ((GTail 7 1 (4 : ℕ) 9 : ℕ) : ZMod 43) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (by decide)
  simpa using h.trans hz

example : ∀ i : Fin 6,
    gtailSelectedCofactorResidue (q := 43) 9 4 (by decide) (by decide) (by decide) i = 28 := by
  intro i
  rw [gtail_selected_cofactor_formula]
  apply (div_eq_iff (by decide)).mpr
  decide
example : ∀ i : Fin 6,
    gtailSelectedCofactorResidue (q := 43) 9 1165 (by decide) (by decide) (by decide) i = 28 := by
  intro i
  rw [gtail_selected_cofactor_formula]
  apply (div_eq_iff (by decide)).mpr
  decide
example : ∀ i j : Fin 6,
    gtailSelectedCofactorResidue (q := 43) 9 1165 (by decide) (by decide) (by decide) i =
    gtailSelectedCofactorResidue (q := 43) 9 1165 (by decide) (by decide) (by decide) j :=
  fun i j => gtail_selected_cofactor_uniform _ _ _ _ _ i j
example : ∀ i : Fin 6,
    gtailSelectedCofactorResidue (q := 43) 9 4 (by decide) (by decide) (by decide) i ≠ 0 :=
  fun i => gtail_selected_cofactor_ne_zero _ _ _ _ _ i
example : ∀ i : Fin 6,
    gtailSelectedCofactorResidue (q := 43) 9 1165 (by decide) (by decide) (by decide) i ≠ 0 :=
  fun i => gtail_selected_cofactor_ne_zero _ _ _ _ _ i

-- Here the formula, rather than the older prime-product nonmember proof, explains exclusion.
example : ∀ i : Fin 6, gtailCyclotomicCofactor 9 4 i ∉ K (sixInverseSlot i) := by
  intro i
  rw [mem_sixRootKernel_iff]
  have h := gtail_selected_cofactor_ne_zero (q := 43) 9 4
    (by decide) (by decide) (by decide) i
  simpa only [gtailSelectedCofactorResidue, ratio4] using h
example : ∀ i : Fin 6, gtailCyclotomicCofactor 9 1165 i ∉ K (sixInverseSlot i) := by
  intro i
  rw [mem_sixRootKernel_iff]
  have h := gtail_selected_cofactor_ne_zero (q := 43) 9 1165
    (by decide) (by decide) (by decide) i
  simpa only [gtailSelectedCofactorResidue, ratio1165] using h

-- Mod-q simple roots coexist with deeper source-element square membership.
example : ∀ i : Fin 6, gtailCyclotomicFactor 9 1165 i ∈ K (sixInverseSlot i) ^ 2 := by
  intro i
  have h := gtailCyclotomicFactor_mem_square_of_sq_dvd_GTail (q := 43) 9 1165
    (by decide) (by decide) (by decide) (by decide) i
  simpa only [ratio1165] using h
example : ∀ i : Fin 6, gtailCyclotomicFactor 9 4 i ∉ K (sixInverseSlot i) ^ 2 := by
  intro i
  have h := gtailCyclotomicFactor_not_mem_square (q := 43) 9 4
    (by decide) (by decide) (by decide) (by decide) i
  simpa only [ratio4] using h

example : (43 : ℕ) ≠ 7 :=
  nontrivial_seventh_root_prime_ne_seven (11 : ZMod 43) (by decide) (by decide)
example : ¬ ∃ r : ZMod 7, r ^ 7 = 1 ∧ r ≠ 1 := by decide
example : (tailShellPoly (1 : ZMod 7)).eval 1 = 0 := by
  norm_num [tailShellPoly_eval, Fin.sum_univ_succ]
  decide
example : (tailShellPoly (1 : ZMod 7)).derivative.eval 1 = 0 := by
  norm_num [tailShellPoly, Fin.sum_univ_succ, derivative_mul, derivative_pow, C_ofNat]
  decide
example : (tailShellPoly (0 : ℤ)).eval 1 = 1 := by
  norm_num [tailShellPoly_eval, Fin.sum_univ_succ]
example : (tailShellPoly (1 : ℤ)).eval 1 = 7 := by
  norm_num [tailShellPoly_eval, Fin.sum_univ_succ]
example (c : ℕ) : (∏ i : Fin 6, gtailCyclotomicFactor c 0 i) =
    ((GTail 7 1 0 c : ℕ) : SevenCyclotomicDegreeSixInt.Ring) :=
  prod_six_gtailCyclotomicFactor_eq_GTail _ _
example : (∏ i : Fin 6, gtailCyclotomicFactor 0 1 i) = 1 := by
  rw [prod_six_gtailCyclotomicFactor_eq_GTail]
  norm_num [GTail, Finset.sum_range_succ, Nat.choose]
example : (43 : ℕ) ∣ 0 := by decide
example : (13 : ℕ) ∣ 13 ∧ ¬ (13 : ℕ) ∣ GTail 7 1 13 30 := by decide
example : gtailSevenTailRatio 13 30 13 = 1 := by
  dsimp [gtailSevenTailRatio]
  apply (div_eq_iff (by decide : (30 : ZMod 13) ≠ 0)).mpr
  decide
example : ¬ Fermat7Equation 5 8 9 := by
  unfold Fermat7Equation
  decide

#print axioms DkMath.FLT.Seven.tailShellPoly
#print axioms DkMath.FLT.Seven.tailShellPoly_eval
#print axioms DkMath.FLT.Seven.tailShellPoly_eval_nat
#print axioms DkMath.FLT.Seven.tailShellPoly_mul
#print axioms DkMath.FLT.Seven.tailShellPoly_derivative_identity
#print axioms DkMath.FLT.Seven.tailShellPoly_derivative_at_zero
#print axioms DkMath.FLT.Seven.gtail_shell_derivative_balance
#print axioms DkMath.FLT.Seven.gtail_shell_derivative_formula
#print axioms DkMath.FLT.Seven.tailShellPoly_eq_root_product
#print axioms DkMath.FLT.Seven.tailShellPoly_derivative_eq_erased_product
#print axioms DkMath.FLT.Seven.eval_selected_cofactor_eq_tailShellPoly_derivative
#print axioms DkMath.FLT.Seven.nontrivial_seventh_root_prime_ne_seven
#print axioms DkMath.FLT.Seven.gtailSelectedCofactorResidue
#print axioms DkMath.FLT.Seven.gtail_selected_cofactor_balance
#print axioms DkMath.FLT.Seven.gtail_selected_cofactor_formula
#print axioms DkMath.FLT.Seven.gtail_selected_cofactor_uniform
#print axioms DkMath.FLT.Seven.gtail_selected_cofactor_ne_zero

end DkMathTest.FLT.Seven.GTailCyclotomicTailDerivative
