/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailCyclotomicSixRootInterpolation
import DkMath.Lib.Cosmic.GTailCyclotomic

#print "file: DkMath.FLT.Seven.GTailCyclotomicTailFactorProduct"

namespace DkMath.FLT.Seven

open DkMath.CosmicFormula DkMath.Lib.NumberTheory SevenCyclotomicDegreeSixInt

/-- The six actual integral factors, indexed by positive proper powers of zeta. -/
def gtailCyclotomicFactor (c g : ℕ) (i : Fin 6) : SevenCyclotomicDegreeSixInt.Ring :=
  ((c + g : ℕ) : SevenCyclotomicDegreeSixInt.Ring) -
    zeta ^ (i.val + 1) * (c : SevenCyclotomicDegreeSixInt.Ring)

theorem gtailCyclotomicFactor_zero (c g : ℕ) :
    gtailCyclotomicFactor c g 0 = gtailCyclotomicLinearFactor c g := by
  simp [gtailCyclotomicFactor, gtailCyclotomicLinearFactor, ofReal]

private theorem geom_of_relations {A : Type*} [CommRing A] (z t : A)
    (hq : z ^ 2 - t * z + 1 = 0) (ht : t ^ 3 + t ^ 2 - 2 * t - 1 = 0) :
    1 + z + z ^ 2 + z ^ 3 + z ^ 4 + z ^ 5 + z ^ 6 = 0 := by
  linear_combination
    (z ^ 4 + z ^ 3 * t + z ^ 3 + z ^ 2 * t ^ 2 + z ^ 2 * t +
      z * t ^ 3 + z * t ^ 2 - z * t + t ^ 4 + t ^ 3 - 2 * t ^ 2 - t + 1) * hq +
    (z * t ^ 2 - z - t) * ht

/-- Seven-term sum in the actual carrier, proved without cancelling zeta minus one. -/
theorem zeta_geom_sum :
    1 + zeta + zeta ^ 2 + zeta ^ 3 + zeta ^ 4 + zeta ^ 5 + zeta ^ 6 = 0 :=
  geom_of_relations zeta (ofReal (SevenRealCubicInt.alpha - 1))
    zeta_quadratic_relation ofReal_alphaSubOne_cubic_relation

private theorem product_of_geom {A : Type*} [CommRing A] (z X Y : A)
    (h : 1 + z + z ^ 2 + z ^ 3 + z ^ 4 + z ^ 5 + z ^ 6 = 0) :
    (∏ i : Fin 6, (X - z ^ (i.val + 1) * Y)) =
      ∑ j : Fin 7, X ^ (6 - j.val) * Y ^ j.val := by
  simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ]
  norm_num
  linear_combination
    (z ^ 15 * Y ^ 6 - z ^ 14 * X * Y ^ 5 - z ^ 14 * Y ^ 6 +
      z ^ 12 * X ^ 2 * Y ^ 4 + z ^ 10 * X ^ 2 * Y ^ 4 - z ^ 9 * X ^ 3 * Y ^ 3 +
      z ^ 8 * X ^ 2 * Y ^ 4 + z ^ 8 * X * Y ^ 5 + z ^ 8 * Y ^ 6 -
      z ^ 7 * X ^ 3 * Y ^ 3 - z ^ 7 * X ^ 2 * Y ^ 4 - z ^ 7 * X * Y ^ 5 -
      z ^ 7 * Y ^ 6 - z ^ 6 * X ^ 3 * Y ^ 3 + z ^ 5 * X ^ 4 * Y ^ 2 +
      z ^ 3 * X ^ 4 * Y ^ 2 + z * X ^ 4 * Y ^ 2 + z * X ^ 3 * Y ^ 3 +
      z * X ^ 2 * Y ^ 4 + z * X * Y ^ 5 + z * Y ^ 6 - X ^ 5 * Y -
      X ^ 4 * Y ^ 2 - X ^ 3 * Y ^ 3 - X ^ 2 * Y ^ 4 - X * Y ^ 5 - Y ^ 6) * h

/-- Unconditional homogeneous source identity for arbitrary elements X and Y. -/
theorem prod_six_zeta_factors_eq_shell (X Y : SevenCyclotomicDegreeSixInt.Ring) :
    (∏ i : Fin 6, (X - zeta ^ (i.val + 1) * Y)) =
      ∑ j : Fin 7, X ^ (6 - j.val) * Y ^ j.val :=
  product_of_geom zeta X Y zeta_geom_sum

/-- The original natural GTail shell, with no gap cancellation or nonzero premise. -/
theorem GTail_seven_one_eq_homogeneous_sum (c g : ℕ) :
    GTail 7 1 g c = ∑ j : Fin 7, (c + g) ^ (6 - j.val) * c ^ j.val := by
  rw [GTail_one_eq_GTailCyclotomicShell]
  simp [GTailCyclotomicShell, Finset.sum_range_succ, Fin.sum_univ_succ]
  ring

/-- Exact element product in the existing degree-six integral ring, including zero gap. -/
theorem prod_six_gtailCyclotomicFactor_eq_GTail (c g : ℕ) :
    (∏ i : Fin 6, gtailCyclotomicFactor c g i) =
      ((GTail 7 1 g c : ℕ) : SevenCyclotomicDegreeSixInt.Ring) := by
  rw [GTail_seven_one_eq_homogeneous_sum]
  simp only [gtailCyclotomicFactor, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]
  exact prod_six_zeta_factors_eq_shell _ _


/-- Evaluation of each integral factor at any supplied nontrivial seventh root. -/
theorem evalCyclotomic_gtailFactor {q : ℕ} [Fact (Nat.Prime q)]
    (s : ZMod q) (hs0 : s ≠ 0) (hs7 : s ^ 7 = 1) (hs1 : s ≠ 1)
    (c g : ℕ) (i : Fin 6) :
    evalCyclotomicFromSeventhRoot s hs0 hs7 hs1 (gtailCyclotomicFactor c g i) =
      ((c + g : ℕ) : ZMod q) - s ^ (i.val + 1) * (c : ZMod q) := by
  simp only [gtailCyclotomicFactor, map_sub, map_mul, map_pow, map_natCast,
    evalCyclotomicFromSeventhRoot_zeta]

/-- Inverse exponent indexing, rather than diagonal factor/kernel alignment. -/
def sixInverseSlot (i : Fin 6) : Fin 6 := ![0, 3, 4, 1, 2, 5] i

theorem sixInverseSlot_involutive : Function.Involutive sixInverseSlot := by
  intro i
  fin_cases i <;> rfl

theorem six_inverse_exponents (i j : Fin 6) :
    (i.val + 1) * (j.val + 1) % 7 = 1 ↔ j = sixInverseSlot i := by
  fin_cases i <;> fin_cases j <;> decide

/-- Canonical Tail factors meet exactly the inverse-exponent prime slot. -/
theorem gtailCyclotomicFactor_mem_sixRootKernel_iff {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c)
    (i j : Fin 6) :
    gtailCyclotomicFactor c g i ∈ sixRootKernel (gtailSevenTailRatio q c g)
      (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
      (gtailSevenTailRatio_ne_one hc hg) j ↔ (i.val + 1) * (j.val + 1) % 7 = 1 := by
  let r := gtailSevenTailRatio q c g
  have hr7 : r ^ 7 = 1 := gtailSevenTailRatio_pow_seven hc hT
  have hr1 : r ≠ 1 := gtailSevenTailRatio_ne_one hc hg
  have hc0 : (c : ZMod q) ≠ 0 := fun h => hc ((ZMod.natCast_eq_zero_iff c q).mp h)
  rw [mem_sixRootKernel_iff, evalCyclotomic_gtailFactor, sub_eq_zero]
  change ((c + g : ℕ) : ZMod q) = (r ^ (j.val + 1)) ^ (i.val + 1) * (c : ZMod q) ↔ _
  have he : ((c + g : ℕ) : ZMod q) = r * (c : ZMod q) := by
    dsimp [r, gtailSevenTailRatio]
    push_cast
    exact (div_mul_cancel₀ _ hc0).symm
  rw [he, mul_left_inj' hc0, ← pow_mul, eq_comm]
  have hf : IsOfFinOrder r := orderOf_pos_iff.mp (by rw [seventhRoot_orderOf r hr7 hr1]; decide)
  have hp := hf.pow_inj_mod (n := (j.val + 1) * (i.val + 1)) (m := 1)
  simpa only [pow_one, seventhRoot_orderOf r hr7 hr1, Nat.one_mod, mul_comm] using hp

/-- Each factor has one actual kernel receiver and excludes all five others. -/
theorem gtailCyclotomicFactor_unique_slot {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c)
    (i j : Fin 6) :
    gtailCyclotomicFactor c g i ∈ sixRootKernel (gtailSevenTailRatio q c g)
      (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
      (gtailSevenTailRatio_ne_one hc hg) j ↔ j = sixInverseSlot i :=
  (gtailCyclotomicFactor_mem_sixRootKernel_iff c g hc hg hT i j).trans (six_inverse_exponents i j)

end DkMath.FLT.Seven
