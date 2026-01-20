/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.Defs
import DkMath.RH.EulerZetaLemmas

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
  unfold eulerZetaFactorMag
  have w_ne_zero : eulerZeta_exp_s_log_p_sub_one p σ t ≠ 0 := by
    apply eulerZeta_exp_s_log_p_sub_one_ne_zero p hp σ
    linarith
  have w_norm_pos : 0 < ‖eulerZeta_exp_s_log_p_sub_one p σ t‖ :=
    norm_pos_iff.mpr w_ne_zero
  have exp_pos : 0 < Real.exp (σ * Real.log (p : ℝ)) := Real.exp_pos _
  -- 分子が正、分母が正なので商も正
  have ratio_pos : 0 < Real.exp (σ * Real.log (p : ℝ)) / ‖eulerZeta_exp_s_log_p_sub_one p σ t‖ :=
    div_pos exp_pos w_norm_pos
  -- 粗い上界：p ≥ 2 のとき、σ > 1 より
  -- eulerZetaFactorMag p σ t = exp(σ*log p) / ‖w‖
  -- 分子は exp(σ*log p) > exp(log 2) = 2（σ > 1, p ≥ 2 より）
  -- 分母は正だから商は制限される
  have p_ge_2 : 2 ≤ p := Nat.Prime.two_le hp
  -- 粗い評価：result ≤ 2 で抑えるために、
  -- 実際には norm_exp_sub_one_lower を使って
  -- ‖w‖ ≥ exp(σ*log p) - 1 ≥ exp(log p) - 1 ≥ 2 - 1 = 1
  -- だから a_p ≤ exp(σ*log p) / 1 のような上界が出る
  -- ただしより正確には...（詳細は省略）
  by_contra h
  push_neg at h
  -- ratio が 2 より大きい場合、norm_exp_sub_one_lower から矛盾を導く
  -- （詳細実装は後で）
  sorry

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
  -- Multipliable は HasProd の存在を意味する
  -- 実装方針：
  -- σ > 1 では、各素数 p に対して
  -- a_p := eulerZetaFactorMag p σ t は 1 に十分に近く、
  -- かつ σ*log(p) > log(p) より指数が支配的
  -- 部分積の極限を使って HasProd を構成する
  --
  -- 詳細：
  -- 1. 部分積 ∏_{p ≤ N} a_p を定義
  -- 2. N → ∞ で収束することを示す
  -- 3. HasProd を構成
  -- （実装は複雑なので、当面プレースホルダー）
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
  -- よって各因子 > 0
  have factor_pos : ∀ p : ℕ, Nat.Prime p → 0 < eulerZetaFactorMag p σ t := by
    intro p hp
    unfold eulerZetaFactorMag
    have exp_pos : 0 < Real.exp (σ * Real.log (p : ℝ)) := Real.exp_pos _
    have w_ne_zero : eulerZeta_exp_s_log_p_sub_one p σ t ≠ 0 :=
      eulerZeta_exp_s_log_p_sub_one_ne_zero p hp σ (by linarith : 0 < σ) t
    have w_norm_pos : 0 < ‖eulerZeta_exp_s_log_p_sub_one p σ t‖ := norm_pos_iff.mpr w_ne_zero
    exact div_pos exp_pos w_norm_pos
  -- tprod は「各因子が正で Multipliable」なら正値
  -- HasProd を使って HasProd.prod_pos のような補題があるが、
  -- ここではダイレクトに正値を示す：
  -- Multipliable ⟹ HasProd が存在 ⟹ 極限値が正（各因子が正のため）
  -- 実装：Finprod や部分積の極限をとって正値を確認
  sorry

end DkMath.RH.EulerZeta
