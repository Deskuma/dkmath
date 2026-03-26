/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.ABC.Basic

#print "file: DkMath.ABC.ABC025_bound2"

set_option linter.style.emptyLine false

/-!
# ABC025: 3→2 への補題集

このファイルでは、`ABC025.lean` の主証明で用いられる補題を
`ABC025` 本体に依存しない形で切り出して定義する。

(目的) `∑_{n=0}^X p^{t·v_p(2n+1)}` の上界を `3(X+1)` から `2(X+1)` に
詰めるための補題群をまとめる。
-/

namespace ABC

open Real

open scoped BigOperators

/-- p ≥ 3, 0 < t ≤ 1/2 のとき、主項係数が 2/3 以下であること。

主項係数:
  ((p^t - 1) / p) / (1 - p^{t-1})
-/
lemma rpow_main_term_le_two_thirds {p : ℕ} [hp : Fact p.Prime] (hp3 : p ≥ 3)
    {t : ℝ} (ht : 0 < t) (ht_half : t ≤ 1 / 2) :
    ((p : ℝ) ^ t - 1) * (p : ℝ) ^ (-1 : ℝ) /
        (1 - (p : ℝ) ^ (t - 1)) ≤
      2 / 3 := by
  have hp_pos : 0 < (p : ℝ) := nat_ge_3_cast_pos hp3
  have hp_ne : (p : ℝ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hp_nonneg : 0 ≤ (p : ℝ) := le_of_lt hp_pos
  -- p^t ≤ √p (t ≤ 1/2)
  have hpt_le_sqrt : (p : ℝ) ^ t ≤ Real.sqrt (p : ℝ) :=
    rpow_t_le_sqrt_nat ht_half (by linarith [hp3])
  have hsqrt_nonneg : 0 ≤ Real.sqrt (p : ℝ) := by positivity
  have hsqrt_pos : 0 < Real.sqrt (p : ℝ) := by
    exact Real.sqrt_pos.mpr hp_pos
  -- 主項係数を 1/√p で抑える
  have hcoeff_le_inv_sqrt :
      ((p : ℝ) ^ t - 1) / ((p : ℝ) - (p : ℝ) ^ t) ≤
        1 / Real.sqrt (p : ℝ) := by
    have hsqrt_le_mid : Real.sqrt (p : ℝ) ≤ ((p + 1 : ℝ) / 2) := sqrt_le_p_add_one_div_two hp3
    have hmid_lt_p : ((p + 1 : ℝ) / 2) < (p : ℝ) := by
      nlinarith [show (3 : ℝ) ≤ (p : ℝ) by exact_mod_cast hp3]
    have hsqrt_lt_p : Real.sqrt (p : ℝ) < (p : ℝ) := lt_of_le_of_lt hsqrt_le_mid hmid_lt_p
    have hpt_lt_p : (p : ℝ) ^ t < (p : ℝ) := lt_of_le_of_lt hpt_le_sqrt hsqrt_lt_p
    have hden_pos : 0 < (p : ℝ) - (p : ℝ) ^ t := sub_pos.mpr hpt_lt_p
    apply (div_le_iff₀ hden_pos).2
    have hsq : (Real.sqrt (p : ℝ)) ^ 2 = (p : ℝ) := by
      simp [Real.sq_sqrt hp_nonneg]
    have hmul : ((p : ℝ) ^ t - 1) * Real.sqrt (p : ℝ) ≤ (p : ℝ) - (p : ℝ) ^ t := by
      nlinarith [hpt_le_sqrt, hsq, hsqrt_nonneg]
    have htmp : (p : ℝ) ^ t - 1 ≤ ((p : ℝ) - (p : ℝ) ^ t) / Real.sqrt (p : ℝ) := by
      exact (le_div_iff₀ hsqrt_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using htmp
  -- 1/√p ≤ 2/3 for p ≥ 3
  have hinv : 1 / Real.sqrt (p : ℝ) ≤ 2 / 3 := by
    have hge : (3 / 2 : ℝ) ≤ Real.sqrt (p : ℝ) := by
      have h3 : (p : ℝ) ≥ 3 := by exact_mod_cast hp3
      have h94_le_p : (9 / 4 : ℝ) ≤ (p : ℝ) := by nlinarith [h3]
      have hsqrt : Real.sqrt (9 / 4 : ℝ) ≤ Real.sqrt (p : ℝ) := Real.sqrt_le_sqrt h94_le_p
      have hsqrt94 : Real.sqrt (9 / 4 : ℝ) = 3 / 2 := by norm_num
      simpa [hsqrt94] using hsqrt
    have h32_pos : (0 : ℝ) < 3 / 2 := by norm_num
    have htmp : 1 / Real.sqrt (p : ℝ) ≤ 1 / (3 / 2 : ℝ) := one_div_le_one_div_of_le h32_pos hge
    norm_num at htmp ⊢
    exact htmp
  have hrewrite :
      ((p : ℝ) ^ t - 1) * (p : ℝ) ^ (-1 : ℝ) /
          (1 - (p : ℝ) ^ (t - 1)) =
        ((p : ℝ) ^ t - 1) / ((p : ℝ) - (p : ℝ) ^ t) := by
    have hpow_sub : (p : ℝ) ^ (t - 1) = (p : ℝ) ^ t / (p : ℝ) := by
      simpa [Real.rpow_one] using (Real.rpow_sub hp_pos t 1)
    have hden_eq : 1 - (p : ℝ) ^ (t - 1) = ((p : ℝ) - (p : ℝ) ^ t) / (p : ℝ) := by
      simpa [hpow_sub] using (one_sub_rpow_sub_one_div hp_pos t)
    rw [Real.rpow_neg_one, hden_eq, ← div_eq_mul_inv]
    field_simp [hp_ne]
  have :
      ((p : ℝ) ^ t - 1) * (p : ℝ) ^ (-1 : ℝ) /
          (1 - (p : ℝ) ^ (t - 1)) ≤
        2 / 3 := by
    have := le_trans hcoeff_le_inv_sqrt hinv
    simpa [hrewrite] using this
  exact this

/-- X ≥ 11 のとき、√(2X+2) - 1 ≤ (X+1)/3 となる不等式。 -/
lemma sqrt_two_X_add_two_sub_one_le_third_X_add_one {X : ℕ} (hX : X ≥ 11) :
    Real.sqrt (2 * (X : ℝ) + 2) - 1 ≤ (X + 1 : ℝ) / 3 := by
  -- 目的不等式を二乗して処理する
  have hpos : 0 ≤ (X + 1 : ℝ) / 3 + 1 := by
    have : 0 ≤ (X : ℝ) := Nat.cast_nonneg X
    nlinarith
  have hsq : 2 * (X : ℝ) + 2 ≤ ((X + 1 : ℝ) / 3 + 1) ^ 2 := by
    have hX' : (X : ℝ) ≥ 11 := by exact_mod_cast hX
    -- 9*(2X+2) ≤ (X+4)^2  ⟺ X^2 - 10X - 2 ≥ 0, which holds for X ≥ 11
    have : 0 ≤ (X : ℝ) ^ 2 - 10 * (X : ℝ) - 2 := by
      have : (X : ℝ) ≥ 11 := hX'
      nlinarith
    nlinarith
  have hroot : Real.sqrt (2 * (X : ℝ) + 2) ≤ (X + 1 : ℝ) / 3 + 1 :=
    Real.sqrt_le_iff.mpr ⟨by positivity, hsq⟩
  linarith

end ABC
