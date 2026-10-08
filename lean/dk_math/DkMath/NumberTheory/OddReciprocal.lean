/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.OddReciprocal"

/-! Finite reciprocal bounds using Mathlib's rational-valued harmonic numbers. -/

namespace DkMath.NumberTheory

open scoped BigOperators

/-- Removing the first reciprocal gives the harmonic number minus one. -/
theorem reciprocal_Icc_two_eq_harmonic_sub_one {L : ℕ} (hL : 1 ≤ L) :
    (∑ a ∈ Finset.Icc 2 L, (1 : ℝ) / (a : ℝ)) = (harmonic L : ℝ) - 1 := by
  have hs : (harmonic L : ℝ) = ∑ a ∈ Finset.Icc 1 L, (1 : ℝ) / (a : ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  rw [hs]
  have he := Finset.sum_erase_add (Finset.Icc 1 L) (fun a : ℕ => (1 : ℝ) / (a : ℝ))
    (Finset.left_mem_Icc.mpr hL)
  simp only [Finset.Icc_erase_left, Nat.cast_one, div_one] at he
  have hI : Finset.Ioc 1 L = Finset.Icc 2 L := by
    ext a; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  rw [hI] at he
  linarith

/-- Odd depths starting at three are a subset of the full harmonic tail. -/
theorem odd_reciprocal_sum_le_full (L : ℕ) :
    (∑ a ∈ (Finset.Icc 3 L).filter Odd, (1 : ℝ) / (a : ℝ)) ≤
      ∑ a ∈ Finset.Icc 2 L, (1 : ℝ) / (a : ℝ) := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro a ha
    have h := Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1
    exact Finset.mem_Icc.mpr ⟨by omega, h.2⟩
  · intro a _ _
    exact div_nonneg zero_le_one (Nat.cast_nonneg a)

/-- The standard harmonic upper bound compresses the finite odd tail. -/
theorem odd_reciprocal_sum_le_log {L : ℕ} (hL : 3 ≤ L) :
    (∑ a ∈ (Finset.Icc 3 L).filter Odd, (1 : ℝ) / (a : ℝ)) ≤ Real.log (L : ℝ) := by
  have ht := odd_reciprocal_sum_le_full L
  rw [reciprocal_Icc_two_eq_harmonic_sub_one (by omega)] at ht
  have hh := harmonic_le_one_add_log L
  linarith

/-- A global logarithmic envelope useful for comparing finite budgets. -/
theorem three_mul_log_le_add_one {x : ℝ} (hx : 0 < x) : 3 * Real.log x ≤ x + 1 := by
  have h3 : Real.log (3 : ℝ) ≤ 4 / 3 := by
    have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 3)
      (by norm_num : (3 : ℝ) ≤ (13 / 9) ^ 3)
    rw [Real.log_pow] at hm
    have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 13 / 9)
    norm_num at hm hl ⊢
    linarith
  have ht := Real.log_le_sub_one_of_pos (div_pos hx (by norm_num : (0 : ℝ) < 3))
  rw [Real.log_div (ne_of_gt hx) (by norm_num)] at ht
  linarith

end DkMath.NumberTheory
