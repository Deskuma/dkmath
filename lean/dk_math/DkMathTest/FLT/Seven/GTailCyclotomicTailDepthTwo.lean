/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailCyclotomicTailDepthTwo

#print "file: DkMathTest.FLT.Seven.GTailCyclotomicTailDepthTwo"

namespace DkMathTest.FLT.Seven.GTailCyclotomicTailDepthTwo

open DkMath.FLT.Seven DkMath.Lib.NumberTheory DkMath.CosmicFormula
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

-- The saturation lemma remains generic in the ring, including rings with zero divisors.
example {A : Type*} [CommRing A] (J : Ideal A) (hJ : J.IsMaximal)
    (U x : A) (hU : U ∉ J) (h : U * x ∈ J ^ 2) : x ∈ J ^ 2 :=
  mem_maximal_square_of_mul_mem J hJ U x hU h
example {A : Type*} [CommRing A] (J : Ideal A) (hJ : J.IsMaximal)
    (x : A) (h : 1 * x ∈ J ^ 2) : x ∈ J ^ 2 :=
  mem_maximal_square_of_mul_mem J hJ 1 x hJ.isPrime.one_notMem h

example (c g : ℕ) (i : Fin 6) :
    gtailCyclotomicCofactor c g i * gtailCyclotomicFactor c g i =
      ((GTail 7 1 g c : ℕ) : SevenCyclotomicDegreeSixInt.Ring) :=
  gtailCyclotomicCofactor_mul_factor _ _ _
example : ∀ i : Fin 6, gtailCyclotomicCofactor 9 4 i ∉ K (sixInverseSlot i) := by
  intro i
  have h := gtailCyclotomicCofactor_not_mem_selected (q := 43) 9 4
    (by decide) (by decide) (by decide) i
  simpa only [ratio4] using h
example : ∀ i : Fin 6, gtailCyclotomicCofactor 9 1165 i ∉ K (sixInverseSlot i) := by
  intro i
  have h := gtailCyclotomicCofactor_not_mem_selected (q := 43) 9 1165
    (by decide) (by decide) (by decide) i
  simpa only [ratio1165] using h

-- All six cofactors have residue28 at their selected roots in both calibrated cases.
example : ∀ i : Fin 6,
    evalCyclotomicFromSeventhRoot (sixSlotRoot (11 : ZMod 43) (sixInverseSlot i))
      (sixSlotRoot_ne_zero _ (by decide) _) (sixSlotRoot_pow_seven _ (by decide) _)
      (sixSlotRoot_ne_one _ (by decide) (by decide) _) (gtailCyclotomicCofactor 9 4 i) = 28 := by
  intro i
  simp only [gtailCyclotomicCofactor, map_prod, evalCyclotomic_gtailFactor]
  revert i
  decide
example : ∀ i : Fin 6,
    evalCyclotomicFromSeventhRoot (sixSlotRoot (11 : ZMod 43) (sixInverseSlot i))
      (sixSlotRoot_ne_zero _ (by decide) _) (sixSlotRoot_pow_seven _ (by decide) _)
      (sixSlotRoot_ne_one _ (by decide) (by decide) _) (gtailCyclotomicCofactor 9 1165 i) = 28 := by
  intro i
  simp only [gtailCyclotomicCofactor, map_prod, evalCyclotomic_gtailFactor]
  revert i
  decide

example : GTail 7 1 (4 : ℕ) 9 = 14491387 := by decide
example : (43 : ℕ) ∣ GTail 7 1 (4 : ℕ) 9 ∧
    ¬ (43 : ℕ) ^ 2 ∣ GTail 7 1 (4 : ℕ) 9 := by decide
example : ∀ i : Fin 6, gtailCyclotomicFactor 9 4 i ∈ K (sixInverseSlot i) ^ 2 ↔
    (43 : ℕ) ^ 2 ∣ GTail 7 1 (4 : ℕ) 9 := by
  intro i
  have h := gtailCyclotomicFactor_mem_square_iff (q := 43) 9 4
    (by decide) (by decide) (by decide) i
  simpa only [ratio4] using h
example : ∀ i : Fin 6, gtailCyclotomicFactor 9 4 i ∉ K (sixInverseSlot i) ^ 2 := by
  intro i
  have h := gtailCyclotomicFactor_mem_square_iff (q := 43) 9 4
    (by decide) (by decide) (by decide) i
  have h' : gtailCyclotomicFactor 9 4 i ∈ K (sixInverseSlot i) ^ 2 ↔
      (43 : ℕ) ^ 2 ∣ GTail 7 1 (4 : ℕ) 9 := by simpa only [ratio4] using h
  exact fun hm => (by decide : ¬ (43 : ℕ) ^ 2 ∣ GTail 7 1 (4 : ℕ) 9) (h'.mp hm)
example : ∀ i : Fin 6, gtailCyclotomicFactor 9 4 i ∈ K (sixInverseSlot i) ∧
    gtailCyclotomicFactor 9 4 i ∉ K (sixInverseSlot i) ^ 2 := by
  intro i
  have h := gtailCyclotomicFactor_depth_one (q := 43) 9 4
    (by decide) (by decide) (by decide) (by decide) i
  simpa only [ratio4] using h

example : GTail 7 1 (1165 : ℕ) 9 = 2638461449052811747 := by decide
example : ¬ (43 : ℕ) ∣ 9 ∧ ¬ (43 : ℕ) ∣ 1165 ∧
    (43 : ℕ) ∣ GTail 7 1 (1165 : ℕ) 9 ∧ (43 : ℕ) ^ 2 ∣ GTail 7 1 (1165 : ℕ) 9 := by
  decide
example : ∀ i : Fin 6, gtailCyclotomicFactor 9 1165 i ∈ K (sixInverseSlot i) ^ 2 := by
  intro i
  have h := gtailCyclotomicFactor_mem_square_of_sq_dvd_GTail (q := 43) 9 1165
    (by decide) (by decide) (by decide) (by decide) i
  simpa only [ratio1165] using h
example : ∀ i : Fin 6, gtailCyclotomicFactor 9 1165 i ∈ K (sixInverseSlot i) ^ 2 ↔
    (43 : ℕ) ^ 2 ∣ GTail 7 1 (1165 : ℕ) 9 := by
  intro i
  have h := gtailCyclotomicFactor_mem_square_iff (q := 43) 9 1165
    (by decide) (by decide) (by decide) i
  simpa only [ratio1165] using h
example : ∀ i j : Fin 6, j ≠ sixInverseSlot i → gtailCyclotomicFactor 9 1165 i ∉ K j := by
  intro i j hj
  have h := gtailCyclotomicFactor_unique_slot (q := 43) 9 1165
    (by decide) (by decide) (by decide) i j
  have h' : gtailCyclotomicFactor 9 1165 i ∈ K j ↔ j = sixInverseSlot i := by
    simpa only [ratio1165] using h
  exact fun hm => hj (h'.mp hm)
example : ∀ i : Fin 6, sixInverseSlot i = ![0, 3, 4, 1, 2, 5] i := fun _ => rfl
example : ∀ j : Fin 6, (1849 : SevenCyclotomicDegreeSixInt.Ring) ∈ K j ^ 2 := by
  intro j
  exact natCast_mem_sixRootKernel_square_of_sq_dvd _ _ _ _ j 1849 (by decide)
example : (∏ i : Fin 6, gtailCyclotomicFactor 9 1165 i) =
    ((GTail 7 1 1165 9 : ℕ) : SevenCyclotomicDegreeSixInt.Ring) :=
  prod_six_gtailCyclotomicFactor_eq_GTail _ _

-- Boundary inputs still satisfy source reconstruction, but not the local unit/support contract.
example (c : ℕ) : (∏ i : Fin 6, gtailCyclotomicFactor c 0 i) =
    ((GTail 7 1 0 c : ℕ) : SevenCyclotomicDegreeSixInt.Ring) :=
  prod_six_gtailCyclotomicFactor_eq_GTail _ _
example : (43 : ℕ) ∣ 0 := by decide
example : (∏ i : Fin 6, gtailCyclotomicFactor 0 1 i) = 1 := by
  rw [prod_six_gtailCyclotomicFactor_eq_GTail]
  norm_num [GTail, Finset.sum_range_succ, Nat.choose]
example : (13 : ℕ) ∣ 13 ∧ ¬ (13 : ℕ) ∣ GTail 7 1 13 30 := by decide
example : gtailSevenTailRatio 13 30 13 = 1 := by
  dsimp [gtailSevenTailRatio]
  apply (div_eq_iff (by decide : (30 : ZMod 13) ≠ 0)).mpr
  decide
example : ¬ ∃ r : ZMod 7, r ^ 7 = 1 ∧ r ≠ 1 := by decide
example : ¬ Fermat7Equation 5 8 9 := by
  unfold Fermat7Equation
  decide

#print axioms DkMath.FLT.Seven.mem_maximal_square_of_mul_mem
#print axioms DkMath.FLT.Seven.gtailCyclotomicCofactor
#print axioms DkMath.FLT.Seven.gtailCyclotomicCofactor_mul_factor
#print axioms DkMath.FLT.Seven.gtailCyclotomicCofactor_not_mem_selected
#print axioms DkMath.FLT.Seven.natCast_mem_sixRootKernel_square_of_sq_dvd
#print axioms DkMath.FLT.Seven.gtailCyclotomicFactor_mem_square_of_sq_dvd_GTail
#print axioms DkMath.FLT.Seven.gtailCyclotomicFactor_mem_square_iff

end DkMathTest.FLT.Seven.GTailCyclotomicTailDepthTwo
