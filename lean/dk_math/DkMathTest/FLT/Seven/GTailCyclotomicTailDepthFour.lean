/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailCyclotomicTailDepthFour

#print "file: DkMathTest.FLT.Seven.GTailCyclotomicTailDepthFour"

namespace DkMathTest.FLT.Seven.GTailCyclotomicTailDepthFour

open DkMath.FLT.Seven DkMath.Lib.NumberTheory DkMath.CosmicFormula SevenCyclotomicDegreeSixInt Polynomial

local instance : Fact (Nat.Prime 43) := ⟨by decide⟩
local notation "K" => sixRootKernel (11 : ZMod 43) (by decide) (by decide) (by decide)

private theorem ratio (g : ℕ) (hg : g = 4 ∨ g = 1165 ∨ g = 32598) :
    gtailSevenTailRatio 43 9 g = 11 := by
  rcases hg with rfl | rfl | rfl <;> dsimp [gtailSevenTailRatio] <;>
    apply (div_eq_iff (by decide : (9 : ZMod 43) ≠ 0)).mpr <;> decide

private theorem derivative28 :
    (tailShellPoly ((9 : ℕ) : ZMod 43)).derivative.eval ((9 + 1165 : ℕ) : ZMod 43) = 28 := by
  have h := gtail_shell_derivative_formula (q := 43) 9 1165 (by decide) (by decide)
  have hv : (7 : ZMod 43) * 1174 ^ 6 / 1165 = 28 := by
    apply (div_eq_iff (by decide : (1165 : ZMod 43) ≠ 0)).mpr
    decide
  exact h.trans hv

private theorem cubic_support : (43 : ℕ) ^ 3 ∣ GTail 7 1 32598 9 := by
  apply (gtail_second_lift_iff_linear 9 1165 17 (by decide)).mpr
  rw [derivative28]
  decide

example : ∀ j : Fin 6, sixRootKernel (11 : ZMod 43) (by decide) (by decide) (by decide) j *
    sixRootKernelComplement (11 : ZMod 43) (by decide) (by decide) (by decide) j =
    cyclotomicScalarIdeal 43 := fun j => sixRootKernel_mul_complement _ _ _ _ j
example : ∀ j : Fin 6, K j ^ 3 ⊔
    sixRootKernelComplement (11 : ZMod 43) (by decide) (by decide) (by decide) j = ⊤ :=
  fun j => sixRootKernel_pow_sup_complement _ _ _ _ j 3
example : ∀ j : Fin 6, K j ^ 2 ⊓ cyclotomicScalarIdeal 43 = cyclotomicScalarIdeal 43 * K j :=
  fun j => sixRootKernel_square_inf_scalar _ _ _ _ j
example : ∀ j : Fin 6, K j ^ 3 ⊓ cyclotomicScalarIdeal 43 = cyclotomicScalarIdeal 43 * K j ^ 2 :=
  fun j => sixRootKernel_cube_inf_scalar _ _ _ _ j
example : ∀ j : Fin 6, ((43 ^ 3 : ℕ) : Ring) ∈ K j ^ 3 := by
  intro j
  exact (natCast_mem_sixRootKernel_cube_iff _ _ _ _ j _).mpr (by decide)
example : ∀ j : Fin 6, ((43 ^ 2 : ℕ) : Ring) ∉ K j ^ 3 := by
  intro j
  rw [natCast_mem_sixRootKernel_cube_iff]
  decide
example : ∀ j : Fin 6, ((43 ^ 2 : ℕ) : Ring) ∈ K j ^ 2 := by
  intro j
  exact (natCast_mem_sixRootKernel_square_iff _ _ _ _ j _).mpr (by decide)
example : ∀ j : Fin 6, (0 : Ring) ∈ K j ^ 3 := fun _ => Ideal.zero_mem _
example : sixInverseSlot = ![0, 3, 4, 1, 2, 5] := rfl

example : ∀ i : Fin 6, gtailCyclotomicFactor 9 4 i ∉ K (sixInverseSlot i) ^ 3 := by
  intro i
  have h := gtailCyclotomicFactor_mem_cube_iff (q := 43) 9 4
    (by decide) (by decide) (by decide) i
  have hr := ratio 4 (by decide)
  simp only [hr] at h
  exact fun hm => (by decide : ¬ (43 : ℕ) ^ 3 ∣ GTail 7 1 4 9) (h.mp hm)
example : ∀ i j : Fin 6, j ≠ sixInverseSlot i → gtailCyclotomicFactor 9 4 i ∉ K j := by
  intro i j hj
  have h := gtailCyclotomicFactor_unique_slot (q := 43) 9 4
    (by decide) (by decide) (by decide) i j
  simp only [ratio 4 (by decide)] at h
  exact fun hm => hj (h.mp hm)

example : ∀ i : Fin 6, gtailCyclotomicFactor 9 1165 i ∉ K (sixInverseSlot i) ^ 3 := by
  intro i
  have h := gtailCyclotomicFactor_mem_cube_iff (q := 43) 9 1165
    (by decide) (by decide) (by decide) i
  have hr := ratio 1165 (by decide)
  simp only [hr] at h
  exact fun hm => (by decide : ¬ (43 : ℕ) ^ 3 ∣ GTail 7 1 1165 9) (h.mp hm)
example : ∀ i j : Fin 6, j ≠ sixInverseSlot i → gtailCyclotomicFactor 9 1165 i ∉ K j := by
  intro i j hj
  have h := gtailCyclotomicFactor_unique_slot (q := 43) 9 1165
    (by decide) (by decide) (by decide) i j
  simp only [ratio 1165 (by decide)] at h
  exact fun hm => hj (h.mp hm)

example : ∀ i : Fin 6, gtailCyclotomicFactor 9 32598 i ∈ K (sixInverseSlot i) ^ 3 := by
  intro i
  have h := gtailCyclotomicFactor_mem_cube_iff (q := 43) 9 32598
    (by decide) (by decide) (by decide) i
  have hr := ratio 32598 (by decide)
  simp only [hr] at h
  exact h.mpr cubic_support
example : ∀ i j : Fin 6, j ≠ sixInverseSlot i → gtailCyclotomicFactor 9 32598 i ∉ K j := by
  intro i j hj
  have h := gtailCyclotomicFactor_unique_slot (q := 43) 9 32598
    (by decide) (by decide) (by decide) i j
  simp only [ratio 32598 (by decide)] at h
  exact fun hm => hj (h.mp hm)

example : ∀ i : Fin 6, gtailCyclotomicFactor 9 4 i ∈ K (sixInverseSlot i) ∧
    gtailCyclotomicFactor 9 4 i ∉ K (sixInverseSlot i) ^ 2 := by
  intro i
  have h := gtailCyclotomicFactor_depth_one (q := 43) 9 4
    (by decide) (by decide) (by decide) (by decide) i
  simpa only [ratio 4 (by decide)] using h
example : ∀ i : Fin 6, gtailCyclotomicFactor 9 1165 i ∈ K (sixInverseSlot i) ^ 2 := by
  intro i
  have h := gtailCyclotomicFactor_mem_square_of_sq_dvd_GTail (q := 43) 9 1165
    (by decide) (by decide) (by decide) (by decide) i
  simpa only [ratio 1165 (by decide)] using h
example : ∀ i : Fin 6,
    gtailSelectedCofactorResidue (q := 43) 9 32598 (by decide) (by decide) (by decide) i = 28 := by
  intro i
  rw [gtail_selected_cofactor_formula]
  apply (div_eq_iff (by decide)).mpr
  decide
example : ∀ d : Fin 43, (43 : ℕ) ^ 3 ∣ GTail 7 1 (1165 + 43 ^ 2 * d.val) 9 → d = 17 := by
  intro d hd
  obtain ⟨t, ht, hu⟩ := existsUnique_gtail_second_digit (q := 43) 9 1165
    (by decide) (by decide) (by decide)
  exact (hu d hd).trans (hu 17 cubic_support).symm
example : ¬ (43 : ℕ) ^ 4 ∣ GTail 7 1 32598 9 := by decide
example : ¬ ∃ r : ZMod 7, r ^ 7 = 1 ∧ r ≠ 1 := by decide
example : ¬ (13 : ℕ) ∣ GTail 7 1 13 30 := by decide
example : (43 : ℕ) ∣ 0 := by decide
example (c : ℕ) : (∏ i : Fin 6, gtailCyclotomicFactor c 0 i) =
    ((GTail 7 1 0 c : ℕ) : Ring) := prod_six_gtailCyclotomicFactor_eq_GTail _ _
example : ¬ Fermat7Equation 5 8 9 := by unfold Fermat7Equation; decide

example : ∀ j : Fin 6, K j ^ 4 ⊓ cyclotomicScalarIdeal 43 = cyclotomicScalarIdeal 43 * K j ^ 3 :=
  fun j => sixRootKernel_fourth_inf_scalar _ _ _ _ j
example : ∀ j : Fin 6, ((43 ^ 4 : ℕ) : Ring) ∈ K j ^ 4 := by
  intro j
  exact (natCast_mem_sixRootKernel_fourth_iff _ _ _ _ j _).mpr (by decide)
example : ∀ j : Fin 6, ((43 ^ 3 : ℕ) : Ring) ∉ K j ^ 4 := by
  intro j
  rw [natCast_mem_sixRootKernel_fourth_iff]
  decide
example : ∀ j : Fin 6, (0 : Ring) ∈ K j ^ 4 := fun _ => Ideal.zero_mem _
example : ∀ i : Fin 6, gtailCyclotomicFactor 9 4 i ∉ K (sixInverseSlot i) ^ 4 := by
  intro i
  have h := gtailCyclotomicFactor_mem_fourth_iff (q := 43) 9 4
    (by decide) (by decide) (by decide) i
  simp only [ratio 4 (by decide)] at h
  exact fun hm => (by decide : ¬ (43 : ℕ) ^ 4 ∣ GTail 7 1 4 9) (h.mp hm)
example : ∀ i : Fin 6, gtailCyclotomicFactor 9 1165 i ∉ K (sixInverseSlot i) ^ 4 := by
  intro i
  have h := gtailCyclotomicFactor_mem_fourth_iff (q := 43) 9 1165
    (by decide) (by decide) (by decide) i
  simp only [ratio 1165 (by decide)] at h
  exact fun hm => (by decide : ¬ (43 : ℕ) ^ 4 ∣ GTail 7 1 1165 9) (h.mp hm)
example : ∀ i : Fin 6, gtailCyclotomicFactor 9 32598 i ∉ K (sixInverseSlot i) ^ 4 := by
  intro i
  have h := gtailCyclotomicFactor_mem_fourth_iff (q := 43) 9 32598
    (by decide) (by decide) (by decide) i
  simp only [ratio 32598 (by decide)] at h
  exact fun hm => (by decide : ¬ (43 : ℕ) ^ 4 ∣ GTail 7 1 32598 9) (h.mp hm)
example : ∀ i : Fin 6, gtailCyclotomicFactor 9 32598 i ∈ K (sixInverseSlot i) ^ 3 ∧
    gtailCyclotomicFactor 9 32598 i ∉ K (sixInverseSlot i) ^ 4 := by
  intro i
  have h := gtailCyclotomicFactor_depth_three (q := 43) 9 32598
    (by decide) (by decide) (by decide) cubic_support (by decide) i
  simpa only [ratio 32598 (by decide)] using h

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
example : (tailShellPoly (9 : ZMod 43)).derivative.eval 13 = 28 := by
  have h := gtail_shell_derivative_formula (q := 43) 9 4 (by decide) (by decide)
  have hv : (7 : ZMod 43) * 13 ^ 6 / 4 = 28 := by
    apply (div_eq_iff (by decide : (4 : ZMod 43) ≠ 0)).mpr
    decide
  exact h.trans hv
example : (tailShellPoly (9 : ZMod 43)).derivative.eval 1174 = 28 := by
  have h := gtail_shell_derivative_formula (q := 43) 9 1165 (by decide) (by decide)
  have hv : (7 : ZMod 43) * 1174 ^ 6 / 1165 = 28 := by
    apply (div_eq_iff (by decide : (1165 : ZMod 43) ≠ 0)).mpr
    decide
  exact h.trans hv
example : (tailShellPoly (9 : ZMod 43)).derivative.eval 32607 = 28 := by
  have h := gtail_shell_derivative_formula (q := 43) 9 32598 (by decide) (by decide)
  have hv : (7 : ZMod 43) * 32607 ^ 6 / 32598 = 28 := by
    apply (div_eq_iff (by decide : (32598 : ZMod 43) ≠ 0)).mpr
    decide
  exact h.trans hv

#print axioms DkMath.FLT.Seven.sixRootKernel_fourth_inf_scalar
#print axioms DkMath.FLT.Seven.natCast_mem_sixRootKernel_fourth_iff
#print axioms DkMath.FLT.Seven.gtailCyclotomicFactor_mem_fourth_iff
#print axioms DkMath.FLT.Seven.gtailCyclotomicFactor_depth_three

end DkMathTest.FLT.Seven.GTailCyclotomicTailDepthFour
