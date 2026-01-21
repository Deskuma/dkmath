/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.Defs
import DkMath.RH.EulerZetaLemmas

--cid: 696f0dea-ce88-8322-9d20-8ce524dcd533

-- ============================================================================

namespace DkMath.RH.EulerZeta

open DkMath.Basic
open scoped Real
open Complex

/-
収束性のモジュール：Euler-zeta の magnitude 版が収束する条件を扱う

主な役割：
1. σ > 1 のときの収束定理
2. 将来的に：より精密な評価（σ ≥ 1/2 への拡張など）
3. 無限積としての "意味付け"
-/

-- ============================================================================
-- 2. w ≠ 0 の条件（σ > 0）
-- ============================================================================

/-- σ > 0 のとき、exp((σ+it) log p) - 1 ≠ 0

   理由: σ > 0 なら |exp((σ+it) log p)| = exp(σ log p) > 1 なので、
         この値が 1 になることはない（位相がどうであれ）
-/
lemma eulerZeta_exp_s_log_p_sub_one_ne_zero (p : ℕ) (hp : Nat.Prime p)
    (σ : ℝ) (hσ : 0 < σ) (t : ℝ) :
    eulerZeta_exp_s_log_p_sub_one p σ t ≠ 0 := by
  unfold eulerZeta_exp_s_log_p_sub_one
  intro hw
  -- eulerZeta_exp_s_log_p_sub_one p σ t = 0 より
  -- exp(vertical σ t * (Real.log (p : ℝ) : ℂ)) = 1
  set log_p := (Real.log (p : ℝ) : ℂ)
  set z := vertical σ t * log_p
  -- w := exp(z) - 1 = 0 ならば exp(z) = 1
  have exp_z_eq_one : Complex.exp z = 1 := by
    -- w = exp(z) - 1 = 0 から exp(z) = 1 を導く
    -- hw : eulerZeta_exp_s_log_p_sub_one p σ t = 0
    -- つまり exp(z) - 1 = 0
    have h : Complex.exp z - 1 = 0 := hw
    have eq : Complex.exp z = Complex.exp z - 1 + 1 := by ring
    rw [h] at eq
    norm_num at eq
    exact eq
  -- ノルムを取る：‖exp(z)‖ = 1
  have norm_eq : ‖Complex.exp z‖ = 1 := by
    simp only [exp_z_eq_one, norm_one]
  -- ‖exp(z)‖ = exp(z.re) という標準補題を使う
  have norm_exp_eq : ‖Complex.exp z‖ = Real.exp (z.re) :=
    Complex.norm_exp _
  rw [norm_exp_eq] at norm_eq
  -- z.re = σ * log p （vertical_mul_log_p_re を使う）
  have z_re : z.re = σ * Real.log (p : ℝ) :=
    vertical_mul_log_p_re p σ t
  rw [z_re] at norm_eq
  -- よって exp(σ * log p) = 1
  have exp_sigma_log_p_eq_one : Real.exp (σ * Real.log (p : ℝ)) = 1 := norm_eq
  -- ⟺ σ * log p = 0 （exp_eq_one_iff_eq_zero を使う）
  have sigma_log_p_eq_zero : σ * Real.log (p : ℝ) = 0 :=
    (exp_eq_one_iff_eq_zero _).mp exp_sigma_log_p_eq_one
  -- だがこれは矛盾：σ > 0 で log p > 0 だから σ * log p ≠ 0
  have : σ * Real.log (p : ℝ) ≠ 0 :=
    sigma_log_p_ne_zero p hp σ hσ
  exact this sigma_log_p_eq_zero

-- ============================================================================
-- 1. σ > 1 での基本的な上界
-- ============================================================================

/-- σ > 1 のとき、eulerZetaFactorMag p σ t は 1 に近い

   直感: σ が 1 より十分大きいとき、
   exp(σ log p) / |exp((σ+it) log p) - 1| ≈ exp(σ log p) / exp(σ log p) = 1 に近づく
-/
lemma eulerZetaFactorMag_bound_sigma_gt_one (p : ℕ) (hp : Nat.Prime p)
    (σ : ℝ) (hσ : 1 < σ) (t : ℝ) :
    eulerZetaFactorMag p σ t ≤ 2 := by
  -- 記号整理
  unfold eulerZetaFactorMag
  set x : ℝ := Real.exp (σ * Real.log (p : ℝ))
  set w : ℂ := eulerZeta_exp_s_log_p_sub_one p σ t
  -- x ≥ 2（p ≥ 2, σ > 1 より）
  have hp2 : (2 : ℕ) ≤ p := Nat.Prime.two_le hp
  have hp2R : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hp_pos : (0 : ℝ) < (p : ℝ) := by
    have : 0 < p := Nat.Prime.pos hp
    exact_mod_cast this
  have hlog : Real.log 2 ≤ Real.log (p : ℝ) :=
    Real.log_le_log (by norm_num) hp2R
  have hσ' : (1 : ℝ) ≤ σ := le_of_lt hσ
  have hp_pos : (0 : ℝ) < (p : ℝ) := by
    have : 0 < p := Nat.Prime.pos hp
    exact_mod_cast this
  have hp_gt_one : (1 : ℝ) < (p : ℝ) := by
    have : 1 < p := by omega
    exact_mod_cast this
  have hlog_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogp_pos : (0 : ℝ) < Real.log (p : ℝ) :=
    Real.log_pos hp_gt_one
  have hx2 : (2 : ℝ) ≤ x := by
    -- exp(log 2) = 2 と単調性
    have h_ineq : Real.log 2 ≤ σ * Real.log (p : ℝ) := by
      -- σ ≥ 1, log p ≥ log 2 より σ*log(p) ≥ log 2
      have h1 : Real.log 2 ≤ Real.log (p : ℝ) := hlog
      have h2 : (1 : ℝ) ≤ σ := hσ'
      have h3 : (0 : ℝ) < σ := by linarith
      calc Real.log 2 ≤ 1 * Real.log (p : ℝ) := by
            simp only [one_mul]; exact h1
          _ ≤ σ * Real.log (p : ℝ) := by
            exact mul_le_mul_of_nonneg_right h2 (le_of_lt hlogp_pos)
    have h_exp : Real.exp (Real.log 2) ≤ Real.exp (σ * Real.log (p : ℝ)) :=
      Real.exp_le_exp.mpr h_ineq
    simp only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h_exp
    exact h_exp
  -- 分母下界：x - 1 ≤ ‖w‖
  have hden : x - 1 ≤ ‖w‖ := by
    -- lemma は `Real.exp (σ*log p) - 1 ≤ ‖w‖`
    simpa [w, x] using (norm_exp_sub_one_lower (p := p) (σ := σ) (t := t))
  -- x / ‖w‖ ≤ x / (x - 1)（分母が大きいほど商は小さい）
  have hxpos : 0 ≤ x := le_of_lt (Real.exp_pos _)
  have hx1pos : 0 < x - 1 := by linarith
  have hdiv : x / ‖w‖ ≤ x / (x - 1) := by
    -- `hden : x - 1 ≤ ‖w‖` と正の値での除算比較を使う
    apply div_le_div_of_nonneg_left hxpos hx1pos hden
  -- x/(x-1) ≤ 2（x ≥ 2 を使う）
  have hfrac : x / (x - 1) ≤ 2 := by
    -- 1/(x-1) ≤ 2/x を使って両辺に x を掛ける
    have hrec : (1 / (x - 1)) ≤ (2 / x) :=
      one_div_pow_sub_one_le_two_div_pow (x := x) hx2
    have hxpos' : 0 ≤ x := hxpos
    have := mul_le_mul_of_nonneg_left hrec hxpos'
    -- x * (1/(x-1)) = x/(x-1), x*(2/x) = 2
    -- ただし x ≠ 0 が必要なら hx2 から出る
    have hxne : x ≠ 0 := by linarith
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hxne] using this
  -- まとめ：x/‖w‖ ≤ x/(x-1) ≤ 2
  have : x / ‖w‖ ≤ 2 := le_trans hdiv hfrac
  -- `x` と `w` を戻す
  simpa [x, w] using this

-- ============================================================================
-- 3. σ > 1 での収束定理（骨組み）
-- ============================================================================

/-- σ > 1 のとき、∏'_{p prime} eulerZetaFactorMag p σ t が収束する

   戦略：
   1. a_p := eulerZetaFactorMag p σ t とする
   2. 0 ≤ a_p - 1 ≤ 1/(p^σ - 1) の評価を示す（分子・分母の評価から）
   3. ∑' |a_p - 1| ≤ ∑' 1/(p^σ - 1) ≤ 2 * ∑' 1/p^σ < ∞ で収束
   4. Multipliable.of_summable_norm で無限積の収束を導く
-/
theorem eulerZetaMag_multipliable_sigma_gt_one (σ : ℝ) (hσ : 1 < σ) (t : ℝ) :
    EulerZetaMagMultipliable σ t := by
  unfold EulerZetaMagMultipliable

  -- a_p := eulerZetaFactorMag p σ t
  let a : {p // Nat.Prime p} → ℝ := fun p => eulerZetaFactorMag p.1 σ t

  -- 目標：Multipliable a
  -- 道筋：Summable (fun p => ‖a p - 1‖) ⟹ Multipliable a

  -- Step 1: 各素数 p に対して a_p ≥ 1 を示す
  have ha_ge_one : ∀ p : {p // Nat.Prime p}, 1 ≤ a p := by
    intro ⟨p, hp⟩
    unfold a eulerZetaFactorMag
    set x := Real.exp (σ * Real.log (↑p : ℝ))
    set w := eulerZeta_exp_s_log_p_sub_one p σ t
    -- x - 1 ≤ ‖w‖ （norm_exp_sub_one_lower）
    have h_den : x - 1 ≤ ‖w‖ := norm_exp_sub_one_lower p σ t
    -- x ≥ 2 （p ≥ 2, σ > 1 より）
    have hx_ge_2 : 2 ≤ x := by
      have hp2 : (2 : ℕ) ≤ p := Nat.Prime.two_le hp
      have hp_gt_one : (1 : ℝ) < p := by
        have : 1 < p := by omega
        exact_mod_cast this
      have h_log : Real.log 2 ≤ Real.log (p : ℝ) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ p))
      have h_ineq : Real.log 2 ≤ σ * Real.log (p : ℝ) := by
        have h1 : Real.log 2 ≤ 1 * Real.log (p : ℝ) := by simp [h_log]
        have h2 : (1 : ℝ) ≤ σ := le_of_lt hσ
        calc Real.log 2 ≤ 1 * Real.log (p : ℝ) := h1
            _ ≤ σ * Real.log (p : ℝ) := by
              apply mul_le_mul_of_nonneg_right h2
              have : (1 : ℝ) ≤ (p : ℝ) := by
                have : 1 ≤ p := by omega
                exact_mod_cast this
              exact Real.log_nonneg this
      have h_exp : Real.exp (Real.log 2) ≤ Real.exp (σ * Real.log (p : ℝ)) :=
        Real.exp_le_exp.mpr h_ineq
      simp only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h_exp
      exact h_exp
    -- x - 1 ≤ ‖w‖ ≤ x より、x/‖w‖ ≥ x/x = 1
    have hx_pos : 0 < x := Real.exp_pos _
    have hxm1_pos : 0 < x - 1 := by linarith
    have hw_norm_pos : 0 < ‖w‖ := by
      have : ‖w‖ ≥ x - 1 := h_den
      linarith
    have : 1 ≤ x / (x - 1) := by
      have h : x - 1 < x := by linarith
      have hneq : (x - 1 : ℝ) ≠ 0 := hxm1_pos.ne'
      have : x / (x - 1) = 1 + 1 / (x - 1) := by field_simp; ring
      rw [this]
      have : 0 < 1 / (x - 1) := div_pos one_pos hxm1_pos
      linarith
    calc 1 ≤ x / (x - 1) := this
        _ ≤ x / ‖w‖ := by
          -- h_den : x - 1 ≤ ‖w‖ より、x / ‖w‖ ≤ x / (x - 1)
          sorry

  -- Step 2: ‖a_p - 1‖ の上界を得る
  have h_summable_norm_sub_one :
      Summable (fun p : {p // Nat.Prime p} => ‖a p - 1‖) := by
    -- ‖a_p - 1‖ ≤ 2 / p^σ という上界を示す必要
    -- これは eulerZetaFactorMag_sub_one_upper_bound から出る
    have h_bound : ∀ p : {p // Nat.Prime p},
        a p - 1 ≤ 2 / Real.exp (σ * Real.log (↑p : ℝ)) := by
      intro p
      unfold a
      -- eulerZetaFactorMag_sub_one_upper_bound p.1 p.2 σ hσ t を使う
      exact eulerZetaFactorMag_sub_one_upper_bound p.1 p.2 σ hσ t

    -- p級数：∑' 1/p^σ は σ > 1 で収束
    -- 証明：素数 p に対して ∑' 1/p^σ は Riemann zeta 関数の無限積因子の和に等しく、
    -- σ > 1 で絶対収束する（深い定理に依存）
    have h_zeta_convergent : Summable (fun p : {p // Nat.Prime p} => 1 / (↑p : ℝ) ^ σ) := by
      -- これは Riemann zeta や Dirichlet series の基本的な事実
      -- 詳細な証明は今後のモジュールで実装予定
      sorry

    -- 係数を含む形：∑' 2/p^σ も収束
    -- スカラー倍の Summable は元の Summable から得られる
    have h_zeta_2_convergent : Summable (fun p : {p // Nat.Prime p} => 2 / (↑p : ℝ) ^ σ) := by
      have : (fun p : {p // Nat.Prime p} => 2 / (↑p : ℝ) ^ σ) =
             (fun p : {p // Nat.Prime p} => (2 : ℝ) * (1 / (↑p : ℝ) ^ σ)) := by
        ext p; ring
      rw [this]
      exact Summable.const_smul h_zeta_convergent 2

    -- ‖a_p - 1‖ を直接上から評価
    have : ∀ p : {p // Nat.Prime p}, ‖a p - 1‖ ≤ 2 / (↑p : ℝ) ^ σ := by
      intro p
      have h_nonneg : 0 ≤ a p - 1 := by linarith [ha_ge_one p]
      have h_norm : ‖a p - 1‖ = a p - 1 := abs_of_nonneg h_nonneg
      rw [h_norm]
      have h1 := h_bound p
      have hp_pos : (0 : ℝ) < ↑p := by
        have : 0 < p.1 := Nat.Prime.pos p.2
        exact_mod_cast this
      -- exp(σ log p) = p^σ：指数法則から
      have h_exp_eq : Real.exp (σ * Real.log (↑p : ℝ)) = (↑p : ℝ) ^ σ := by
        rw [Real.rpow_def_of_pos hp_pos, mul_comm]
      rw [h_exp_eq] at h1
      exact h1

    -- Summable 由比較判定法
    exact Summable.of_nonneg_of_le (fun p => norm_nonneg _) this h_zeta_2_convergent

  -- Step 3: Summable (‖a_p - 1‖) から Multipliable a を導く
  -- Mathlib の定理：∑' ‖a_p - 1‖ が収束 ⟹ ∏' a_p が Multipliable
  -- これは `Multipliable.of_summable_norm` または類似の形で得られる
  -- 正確な補題名は Mathlibで確認が必要
  sorry

/-- σ > 1 のとき、eulerZetaMag σ t は有限の正の値に収束する

   戦略：
   1. eulerZetaMag_multipliable_sigma_gt_one から Multipliable を取得
   2. 各因子 eulerZetaFactorMag p σ t > 0 を確認
   3. 無限積が収束し、かつ各因子が正ならば積も正
-/
theorem eulerZetaMag_pos_sigma_gt_one (σ : ℝ) (hσ : 1 < σ) (t : ℝ) :
    0 < eulerZetaMag σ t := by
  unfold eulerZetaMag
  -- eulerZetaMag_multipliable_sigma_gt_one から無限積が収束
  have mult := eulerZetaMag_multipliable_sigma_gt_one σ hσ t

  -- 各因子 eulerZetaFactorMag p σ t > 0：
  -- - 分子 exp(σ*log p) > 0（指数は常に正）
  -- - 分母 ‖w‖ > 0（w ≠ 0 から）
  have factor_pos : ∀ p : ℕ, Nat.Prime p → 0 < eulerZetaFactorMag p σ t := by
    intro p hp
    unfold eulerZetaFactorMag
    have exp_pos : 0 < Real.exp (σ * Real.log (p : ℝ)) := Real.exp_pos _
    have w_ne_zero : eulerZeta_exp_s_log_p_sub_one p σ t ≠ 0 :=
      eulerZeta_exp_s_log_p_sub_one_ne_zero p hp σ (by linarith : 0 < σ) t
    have w_norm_pos : 0 < ‖eulerZeta_exp_s_log_p_sub_one p σ t‖ := norm_pos_iff.mpr w_ne_zero
    exact div_pos exp_pos w_norm_pos

  -- Multipliable かつ各因子が正なら、無限積は正値
  -- mult : Multipliable a
  -- factor_pos : ∀ p, 0 < eulerZetaFactorMag p σ t
  -- したがって ∏' a は正値
  sorry

end DkMath.RH.EulerZeta
