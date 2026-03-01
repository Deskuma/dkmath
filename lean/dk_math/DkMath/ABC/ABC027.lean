/-
Copyright (c) 2025 D. and Wise Wolf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.ABC026

#print "file: DkMath.ABC.ABC027"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/- Note:
※細分化前にエラー／警告を出さない補題・定理ファイル。
  ABC.lean で定義されるべき定理のうち、ABC.lean 内で定義されていた定理をここに移動している。
-/

namespace ABC

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

-- ========================================================================
-- Main density-one bound for twoTail
-- ========================================================================

-- private lemmas

/-
Helper lemmas about ceilings used in heavy-prime counting.
These are intentionally placed privately near the top of the file
so downstream proofs can reuse them. We avoid referencing any
project-specific `S_heavy` here: the lemmas only require the
elementwise condition `p ^ 3 > X` which is available at call sites.
-/
lemma ceil_div_le_one_of_p3_gt_X {X p : ℕ} (hp3 : p ^ 3 > X) :
  ⌈(X : ℝ) / (p ^ 3 : ℝ)⌉₊ ≤ 1 := by
  -- Cast the nat-inequality to the reals and divide both sides by p^3 > 0.
  have h_real : (X : ℝ) < (p ^ 3 : ℝ) := by exact_mod_cast hp3
  have hX_nonneg : 0 ≤ (X : ℝ) := by exact_mod_cast (Nat.zero_le X)
  have hpos : 0 < (p ^ 3 : ℝ) := by linarith [h_real, hX_nonneg]
  have hlt : (X : ℝ) / (p ^ 3 : ℝ) < (1 : ℝ) := (div_lt_one hpos).mpr h_real
  have hle : (X : ℝ) / (p ^ 3 : ℝ) ≤ (1 : ℝ) := le_of_lt hlt
  have hle_cast : (X : ℝ) / (p ^ 3 : ℝ) ≤ (↑(1 : ℕ) : ℝ) := by simpa [Nat.cast_one] using hle
  exact Nat.ceil_le.mpr hle_cast

lemma term_le_four_of_p3_gt_X {X p : ℕ} (hp3 : p ^ 3 > X) :
  (2 * ⌈(X : ℝ) / (p ^ 3 : ℝ)⌉₊ + 2) ≤ 4 := by
  have h := ceil_div_le_one_of_p3_gt_X hp3
  calc
    2 * ⌈(X : ℝ) / (p ^ 3 : ℝ)⌉₊ + 2 ≤ 2 * 1 + 2 := by
      apply Nat.add_le_add_right
      apply Nat.mul_le_mul_left
      exact h
    _ = 4 := by norm_num

-- Arithmetic lemma: For X ≥ 1, we have ⌈X/4⌉ ≥ 1, hence 2*⌈X/4⌉+2 ≥ 4
lemma four_le_two_ceil_quarter_add_two {X : ℕ} (hX : X ≥ 1) :
  4 ≤ 2 * ⌈(X : ℝ) / 4⌉₊ + 2 := by
  -- Since X ≥ 1 we have (X/4) > 0, so its ceiling is at least 1
  have hpos : 0 < X := by
    have : 0 < 1 := by norm_num
    exact Nat.lt_of_lt_of_le this hX
  have hy_pos : 0 < (X : ℝ) / 4 := by
    apply _root_.div_pos
    · exact_mod_cast hpos
    · norm_num
  have h_nonneg : 0 ≤ (X : ℝ) / 4 := le_of_lt hy_pos
  have hspec := Nat.ceil_spec ((X : ℝ) / 4) h_nonneg
  have hceil_pos : 0 < (⌈(X : ℝ) / 4⌉₊ : ℝ) := lt_of_lt_of_le hy_pos hspec.2
  have hnat_pos : 0 < ⌈(X : ℝ) / 4⌉₊ := by exact_mod_cast hceil_pos
  have h_one_le : 1 ≤ ⌈(X : ℝ) / 4⌉₊ := Nat.succ_le_of_lt hnat_pos
  calc
    4 = 2 * 1 + 2 := by norm_num
    _ ≤ 2 * ⌈(X : ℝ) / 4⌉₊ + 2 := by
      apply Nat.add_le_add_right
      apply Nat.mul_le_mul_left
      exact h_one_le

-- Budget allocation lemma: B * ⌈f/(B+1)⌉ ≤ ⌈f⌉ for B=4 and f ≥ 20
-- This ensures that B*K_heavy ≤ K_full in the budget split strategy
lemma B_mul_ceil_div_le_ceil_of_large (f : ℝ) (hf : f ≥ 20) :
  4 * ⌈f / 5⌉₊ ≤ ⌈f⌉₊ := by
  -- Strategy: For f ≥ 20, show 4*⌈f/5⌉ ≤ ⌈f⌉
  -- Key: ⌈f/5⌉ < f/5 + 1, so 4*⌈f/5⌉ < 4*(f/5 + 1) = 4f/5 + 4
  -- Need: 4f/5 + 4 ≤ f, which gives: 4 ≤ f/5, i.e., f ≥ 20 ✓
  have hf_div_pos : 0 ≤ f / 5 := by linarith
  have h1 : (⌈f / 5⌉₊ : ℝ) < f / 5 + 1 := Nat.ceil_lt_add_one hf_div_pos
  have h2 : 4 * (⌈f / 5⌉₊ : ℝ) < 4 * (f / 5 + 1) := by linarith
  have h3 : 4 * (f / 5 + 1) = 4 * f / 5 + 4 := by ring
  have h4 : 4 * f / 5 + 4 ≤ f := by linarith  -- Uses hf : f ≥ 20
  have h5 : (⌈f⌉₊ : ℝ) ≥ f := Nat.le_ceil f
  have h6 : 4 * (⌈f / 5⌉₊ : ℝ) < f := by linarith
  have h7 : 4 * (⌈f / 5⌉₊ : ℝ) < (⌈f⌉₊ : ℝ) := by linarith
  -- Convert strict inequality to ≤ for natural numbers
  exact Nat.cast_lt.mp (by exact_mod_cast h7) |>.le

-- Eventually, X^(3/4+ε') ≥ 20 for any ε' > 0
-- This is used to apply B_mul_ceil_div_le_ceil_of_large in the budget allocation
lemma eventually_pow_ge_twenty (ε' : ℝ) (hε' : 0 < ε') :
  ∀ᶠ X : ℕ in atTop, (X : ℝ)^(3/4 + ε') ≥ 20 := by
  -- Strategy: X^(3/4+ε') is monotone increasing and unbounded, so eventually ≥ 20
  -- For X ≥ 100, we have X^(3/4+ε') ≥ 100^(3/4+ε') and 100^(3/4) ≈ 31.6 > 20
  refine eventually_atTop.mpr ⟨100, fun X hX => ?_⟩
  have h1 : (100 : ℝ) ≤ (X : ℝ) := Nat.cast_le.mpr hX
  have h2 : (100 : ℝ)^(3/4 + ε') ≤ (X : ℝ)^(3/4 + ε') := by
    apply Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 100) h1 (by linarith : 0 ≤ 3/4 + ε')
  have h3 : (20 : ℝ) ≤ (100 : ℝ)^(3/4 + ε') := by
    -- 100^(3/4) ≈ 31.6 > 20, and ε' > 0 makes it even larger
    -- Strategy: 100 > 64 = 2^6, so 100^(3/4) > 64^(3/4) = 2^(9/2) = 16√2 > 22 > 20
    have h64 : (64 : ℝ) = (2 : ℝ)^6 := by norm_num
    have h64_pow : (64 : ℝ)^(3/4 : ℝ) = (2 : ℝ)^(9/2 : ℝ) := by
      rw [h64]
      rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have h2_pow : (2 : ℝ)^(9/2 : ℝ) = 16 * Real.sqrt 2 := by
      have : (9 : ℝ) / 2 = 4 + 1/2 := by norm_num
      rw [this, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      simp only [show (2 : ℝ)^(4 : ℝ) = 16 by norm_num]
      -- 2^(1/2) = √2 を示す: (2^(1/2))^2 = 2 であり √2 の定義から従う
      have hsqrt : (2 : ℝ)^(1/2 : ℝ) = Real.sqrt 2 := by
        rw [← Real.sqrt_eq_rpow]
      rw [hsqrt]
    have h_sqrt2_gt : (1.4 : ℝ) < Real.sqrt 2 := by
      have h14_sq : (1.4 : ℝ) ^ 2 = 1.96 := by norm_num
      have : (1.4 : ℝ) ^ 2 < 2 := by rw [h14_sq]; norm_num
      exact Real.lt_sqrt_of_sq_lt this
    have h64_gt_20 : (20 : ℝ) < (64 : ℝ)^(3/4 : ℝ) := by
      rw [h64_pow, h2_pow]
      calc (20 : ℝ)
        < 16 * 1.4 := by norm_num
        _ < 16 * Real.sqrt 2 := by apply mul_lt_mul_of_pos_left h_sqrt2_gt; norm_num
    have h100_gt_64 : (64 : ℝ)^(3/4 : ℝ) < (100 : ℝ)^(3/4 : ℝ) := by
      apply Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ 64) (by norm_num : (64 : ℝ) < 100) (by norm_num : (0 : ℝ) < 3/4)
    have h100_base : (20 : ℝ) < (100 : ℝ)^(3/4 : ℝ) := calc (20 : ℝ)
      _ < (64 : ℝ)^(3/4 : ℝ) := h64_gt_20
      _ < (100 : ℝ)^(3/4 : ℝ) := h100_gt_64
    have h_exp_mono : (100 : ℝ)^(3/4 : ℝ) ≤ (100 : ℝ)^(3/4 + ε') := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 100)
      linarith
    linarith
  linarith

end ABC
