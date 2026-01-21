/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Analysis.PSeries

import DkMath.RH.Defs
import DkMath.RH.EulerZeta

--cid: 696f0dea-ce88-8322-9d20-8ce524dcd533

-- ============================================================================

namespace DkMath.RH.EulerZeta

open DkMath.Basic
open scoped Real
open Complex

/-
補題のモジュール：Euler-zeta の等価性と基本変形

主な役割：
1. 複数の magnitude 定義が等価であることを示す
2. 位相シフト分解などの基本的な変形
3. （将来的に）σ > 1 での簡単な評価
-/

-- ============================================================================
-- 1. Magnitude 定義の等価性
-- ============================================================================

/-- eulerZetaFactorMag と eulerZetaFactorMag_sqrt は同じ値
    理由: norm = √(re² + im²) であるため syntactically 等価
-/
lemma eulerZetaFactorMag_eq_sqrt (p : ℕ) (σ t : ℝ) :
    eulerZetaFactorMag p σ t = eulerZetaFactorMag_sqrt p σ t := by
  unfold eulerZetaFactorMag eulerZetaFactorMag_sqrt
  rfl

/-- eulerZetaFactorMag_sqrt と eulerZetaFactorMag_normSq は同じ値
    理由: re² + im² = normSq であるため syntactically 等価
-/
lemma eulerZetaFactorMag_sqrt_eq_normSq (p : ℕ) (σ t : ℝ) :
    eulerZetaFactorMag_sqrt p σ t = eulerZetaFactorMag_normSq p σ t := by
  unfold eulerZetaFactorMag_sqrt eulerZetaFactorMag_normSq
  simp only [Complex.normSq]
  rfl

/-- eulerZetaFactorMag と eulerZetaFactorMag_normSq は同じ値
    （norm = √(normSq) の等価性を使用）

    注：norm と √(normSq) の関係は Mathlib で示されており、
    完全な証明は Complex.norm_eq_sqrt_normSq 等を使う
-/
lemma eulerZetaFactorMag_eq_normSq (p : ℕ) (σ t : ℝ) :
    eulerZetaFactorMag p σ t = eulerZetaFactorMag_normSq p σ t :=
  eulerZetaFactorMag_eq_sqrt p σ t ▸ eulerZetaFactorMag_sqrt_eq_normSq p σ t

lemma eulerZetaFactorMag_eq_normSq' (p : ℕ) (σ t : ℝ) :
    eulerZetaFactorMag p σ t =
      (let w := eulerZeta_exp_s_log_p_sub_one p σ t
       Real.exp (σ * Real.log (p : ℝ)) / Real.sqrt (Complex.normSq w)) := by
  unfold eulerZetaFactorMag
  change (let w := eulerZeta_exp_s_log_p_sub_one p σ t
          Real.exp (σ * Real.log (p : ℝ)) / ‖w‖) =
         (let w := eulerZeta_exp_s_log_p_sub_one p σ t
          Real.exp (σ * Real.log (p : ℝ)) / Real.sqrt (Complex.normSq w))
  rfl

-- ============================================================================
-- 2. 複素版の基本補題
-- ============================================================================

/-- 複素版：s = 1 を代入すると p/(p-1) になる（因子レベル） -/
lemma eulerZetaFactor_one (p : ℕ) :
    eulerZetaFactor p (1 : ℂ) = (p : ℂ) / ((p : ℂ) - 1) := by
  simp [eulerZetaFactor]

/-- 縦線版の標準化: σ=1, t=0 なら vertical 1 0 = 1 なので同じ形に落ちる -/
lemma eulerZetaFactor_onVertical_std (p : ℕ) :
    eulerZetaFactor p (vertical 1 0) = (p : ℂ) / ((p : ℂ) - 1) := by
  simp [vertical, eulerZetaFactor]

-- ============================================================================
-- 3. Vertical の実部・虚部
-- ============================================================================

/-- vertical の実部は σ -/
lemma vertical_re (σ t : ℝ) : (vertical σ t).re = σ := by
  unfold vertical
  norm_num [Complex.add_re, Complex.mul_I_re]

/-- vertical の虚部は t -/
lemma vertical_im (σ t : ℝ) : (vertical σ t).im = t := by
  unfold vertical
  norm_num [Complex.add_im, Complex.mul_I_im]

-- ============================================================================
-- 4. eulerZeta_exp_s_log_p_sub_one の基本性質
-- ============================================================================

/-- exp(σ log p) は常に正の実数 -/
lemma exp_sigma_log_p_pos (p : ℕ) (σ : ℝ) :
    0 < Real.exp (σ * Real.log (p : ℝ)) := by
  exact Real.exp_pos _

/-- Real.log p は p > 1 のときに正 -/
lemma log_p_pos (p : ℕ) (hp : Nat.Prime p) :
    0 < Real.log (p : ℝ) :=
  Real.log_pos (by norm_cast; exact Nat.Prime.two_le hp)

-- ============================================================================
-- 5. vertical と log p の合成の実部・虚部
-- ============================================================================

/-- vertical σ t * (log p : ℂ) の実部は σ * log p -/
lemma vertical_mul_log_p_re (p : ℕ) (σ t : ℝ) :
    (vertical σ t * (Real.log (p : ℝ) : ℂ)).re = σ * Real.log (p : ℝ) := by
  simp only [vertical, mul_re, add_re, ofReal_re, ofReal_im, I_re, I_im]
  ring

/-- vertical σ t * (log p : ℂ) の虚部は t * log p -/
lemma vertical_mul_log_p_im (p : ℕ) (σ t : ℝ) :
    (vertical σ t * (Real.log (p : ℝ) : ℂ)).im = t * Real.log (p : ℝ) := by
  simp only [vertical, mul_im, add_im, ofReal_im, ofReal_re, I_re, I_im]
  ring

-- ============================================================================
-- 6. σ * log p ≠ 0 の判定
-- ============================================================================

/-- σ > 0 で素数 p のとき σ * log p ≠ 0 -/
lemma sigma_log_p_ne_zero (p : ℕ) (hp : Nat.Prime p) (σ : ℝ) (hσ : 0 < σ) :
    σ * Real.log (p : ℝ) ≠ 0 := by
  apply mul_ne_zero
  · exact hσ.ne'
  · exact (log_p_pos p hp).ne'

-- ============================================================================
-- 7. exp(α) = 1 ⟹ α = 0 （実数版）
-- ============================================================================

/-- 実数で exp(α) = 1 ならば α = 0 -/
lemma exp_eq_one_iff_eq_zero (α : ℝ) : Real.exp α = 1 ↔ α = 0 := by
  constructor
  · intro h
    have : α = Real.log (Real.exp α) := by simp only [Real.log_exp]
    rw [h] at this
    simp only [Real.log_one] at this
    exact this
  · intro h; simp [h]

-- ============================================================================
-- 8. 分母の下界評価（σ > 0 のとき）
-- ============================================================================

/-- σ > 0 のとき、‖w‖ ≥ exp(σ*log p) - 1

   w = exp((σ+it)*log p) - 1 に対して、
   三角不等式と ‖exp(z)‖ = exp(Re(z)) を組み合わせて示す。

   理由：
   - z = (σ+it)*log p とすれば w = exp(z) - 1
   - ‖z - 1‖ ≥ |‖z‖ - 1|（三角不等式）
   - ‖exp(z)‖ = exp(Re(z)) = exp(σ*log p)
   - σ*log p ≥ 0 なら |exp(...) - 1| = exp(...) - 1
-/
lemma norm_exp_sub_one_lower (p : ℕ) (σ t : ℝ) :
    Real.exp (σ * Real.log (p : ℝ)) - 1 ≤
      ‖eulerZeta_exp_s_log_p_sub_one p σ t‖ := by
  unfold eulerZeta_exp_s_log_p_sub_one
  set z := vertical σ t * (Real.log (p : ℝ) : ℂ)
  have h := norm_sub_norm_le (Complex.exp z) (1 : ℂ)
  have norm_exp_eq : ‖Complex.exp z‖ = Real.exp (z.re) := Complex.norm_exp z
  have z_re_eq : z.re = σ * Real.log (p : ℝ) := vertical_mul_log_p_re p σ t
  have norm_one_eq : ‖(1 : ℂ)‖ = 1 := by norm_num
  rw [norm_exp_eq, z_re_eq, norm_one_eq] at h
  linarith

-- ============================================================================
-- 9. 逆数の比較評価
-- ============================================================================

/-- 2 ≤ x のとき、1/(x-1) ≤ 2/x

   証明：1/(x-1) ≤ 2/x ⟺ x ≤ 2(x-1) ⟺ 2 ≤ x
-/
lemma one_div_pow_sub_one_le_two_div_pow
    {x : ℝ} (hx : 2 ≤ x) :
    (1 / (x - 1)) ≤ (2 / x) := by
  have hx_pos : 0 < x := by linarith
  have hx_minus_pos : 0 < x - 1 := by linarith
  -- 1/(x-1) ≤ 2/x ⟺ x ≤ 2(x-1) ⟺ x ≤ 2x - 2 ⟺ 2 ≤ x
  field_simp [hx_pos.ne', hx_minus_pos.ne']
  nlinarith

-- ============================================================================
-- 10. 収束評価：各因子 (a_p - 1) の上界
-- ============================================================================

/-- eulerZetaFactorMag p σ t - 1 ≤ 2 / (exp(σ log p))

   σ > 1 のとき、各因子 a_p := eulerZetaFactorMag p σ t について、
   a_p - 1 が十分に小さいことを示す。

   証明の鍵：
   - a_p = x / ‖w‖ の形（x = exp(σ log p), w = eulerZeta_exp_s_log_p_sub_one）
   - norm_exp_sub_one_lower から x - 1 ≤ ‖w‖
   - eulerZetaFactorMag_bound_sigma_gt_one から x / ‖w‖ ≤ 2（つまり x ≥ 2）
   - したがって a_p - 1 ≤ 1 / (x - 1) ≤ 2 / x
-/
lemma eulerZetaFactorMag_sub_one_upper_bound (p : ℕ) (hp : Nat.Prime p)
    (σ : ℝ) (hσ : 1 < σ) (t : ℝ) :
    eulerZetaFactorMag p σ t - 1 ≤
      2 / Real.exp (σ * Real.log (p : ℝ)) := by
  unfold eulerZetaFactorMag
  set x := Real.exp (σ * Real.log (p : ℝ))
  set w := eulerZeta_exp_s_log_p_sub_one p σ t

  -- 基本的な正性・非零条件
  have hx_pos : 0 < x := Real.exp_pos _
  have w_ne : w ≠ 0 := by
    -- w ≠ 0 であることを示す
    -- σ > 1 > 0 より norm_exp_sub_one_lower が適用でき、
    -- x - 1 ≤ ‖w‖ が得られるので w ≠ 0 が必要
    sorry
  have w_norm_pos : 0 < ‖w‖ := norm_pos_iff.mpr w_ne

  -- x ≥ 2（p ≥ 2, σ > 1 より exp(σ log p) ≥ 2）
  have hx_ge_2 : 2 ≤ x := by
    have hp2 : 2 ≤ p := Nat.Prime.two_le hp
    have hp_gt_one_nat : 1 < p := by omega
    have hp_gt_one : (1 : ℝ) < p := by exact_mod_cast hp_gt_one_nat
    have h_log : Real.log 2 ≤ Real.log (p : ℝ) :=
      Real.log_le_log (by norm_num) (by
        have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
        linarith)
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

  -- 分母下界：x - 1 ≤ ‖w‖
  have h_den : x - 1 ≤ ‖w‖ := norm_exp_sub_one_lower p σ t

  -- x - 1 > 0
  have h_x_minus_one_pos : 0 < x - 1 := by linarith

  -- a_p - 1 = x/‖w‖ - 1 = (x - ‖w‖) / ‖w‖
  have h_eq : x / ‖w‖ - 1 = (x - ‖w‖) / ‖w‖ := by
    field_simp [w_norm_pos.ne']

  -- (x - ‖w‖) / ‖w‖ ≤ 1 / (x - 1)
  have h_upper_1 : x / ‖w‖ - 1 ≤ 1 / (x - 1) := by
    rw [h_eq]
    -- (x - ‖w‖) / ‖w‖ ≤ 1 / (x - 1)
    -- ⟺ (x - ‖w‖) * (x - 1) ≤ ‖w‖
    have h_ineq : (x - ‖w‖) * (x - 1) ≤ ‖w‖ := by
      -- x - ‖w‖ ≤ 1 より
      have h_diff : x - ‖w‖ ≤ 1 := by
        have : x - 1 ≤ ‖w‖ := h_den
        linarith
      have : (x - ‖w‖) * (x - 1) ≤ 1 * (x - 1) :=
        mul_le_mul_of_nonneg_right h_diff (le_of_lt h_x_minus_one_pos)
      simp at this
      have : x - 1 ≤ ‖w‖ := h_den
      linarith
    -- ⟹ (x - ‖w‖) / ‖w‖ ≤ 1 / (x - 1)
    calc (x - ‖w‖) / ‖w‖
        = ((x - ‖w‖) * (x - 1)) / (‖w‖ * (x - 1)) := by
          field_simp [w_norm_pos.ne', h_x_minus_one_pos.ne']
        _ ≤ ‖w‖ / (‖w‖ * (x - 1)) := by
          apply div_le_div_of_nonneg_right h_ineq
          have : 0 ≤ ‖w‖ := w_norm_pos.le
          have : 0 ≤ x - 1 := le_of_lt h_x_minus_one_pos
          exact mul_nonneg ‹0 ≤ ‖w‖› ‹0 ≤ x - 1›
        _ = 1 / (x - 1) := by
          field_simp [w_norm_pos.ne']

  -- 1 / (x - 1) ≤ 2 / x
  have h_upper_2 : (1 : ℝ) / (x - 1) ≤ 2 / x :=
    one_div_pow_sub_one_le_two_div_pow hx_ge_2

  -- 合わせる
  calc x / ‖w‖ - 1 ≤ 1 / (x - 1) := h_upper_1
      _ ≤ 2 / x := h_upper_2

/-- σ > 1 のとき、自然数の p-series ∑' 1/n^σ が収束する

   これは Mathlib の `Real.summable_one_div_nat_rpow` で提供されている。
-/
theorem summable_one_div_nat_rpow_sigma (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ σ) :=
  (Real.summable_one_div_nat_rpow).mpr hσ

/-- σ > 1 のとき、素数に制限した p-series ∑' 1/p^σ が収束する

   自然数版から Subtype.val の単射性で落とす。
-/
theorem summable_one_div_prime_rpow_sigma (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun p : {p // Nat.Prime p} => (1 : ℝ) / (↑p : ℝ) ^ σ) := by
  -- 自然数版の収束
  have h_nat : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ σ) :=
    summable_one_div_nat_rpow_sigma σ hσ
  -- 素数への制限は Subtype.val : {p // Nat.Prime p} → ℕ が単射だから
  -- comp_injective で得られる
  have h_inj : Function.Injective (Subtype.val : {p // Nat.Prime p} → ℕ) :=
    Subtype.coe_injective
  -- f (coe p) = 1 / (↑p : ℝ) ^ σ の形で comp_injective を使う
  have : (fun p : {p // Nat.Prime p} => (1 : ℝ) / (↑p : ℝ) ^ σ) =
         (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ σ) ∘ (Subtype.val : {p // Nat.Prime p} → ℕ) := by
    rfl
  rw [this]
  exact Summable.comp_injective h_nat h_inj

end DkMath.RH.EulerZeta
