/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- cid: 696f0dea-ce88-8322-9d20-8ce524dcd533
-- cid: 69b29c85-0a0c-83a7-aa18-c44fbc8c3399

import Mathlib.Analysis.PSeries
import DkMath.RH.Defs
import DkMath.RH.EulerZeta
import DkMath.RH.Lemmas

#print "file: DkMath.RH.EulerZetaLemmas"

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
    have h_den : x - 1 ≤ ‖w‖ := norm_exp_sub_one_lower p σ t
    -- x = exp(σ * log p) > 1 since σ > 1 and log p > 0 for prime p ≥ 2
    have h_log_pos : 0 < Real.log (p : ℝ) := log_p_pos p hp
    have hσ_pos : 0 < σ := by linarith [hσ]
    have h_prod_pos : 0 < σ * Real.log (p : ℝ) := mul_pos hσ_pos h_log_pos
    have h_x_gt_one : 1 < x := by simpa [x] using Real.exp_lt_exp.mpr h_prod_pos
    have h_x_minus_one_pos : 0 < x - 1 := by linarith [h_x_gt_one]
    have hw_pos : 0 < ‖w‖ := by linarith [h_den, h_x_minus_one_pos]
    exact (norm_pos_iff.mp hw_pos)
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

-- ============================================================================
-- 11. HOPC-RH: 単一素数因子 `w_p` の位相 API（RH-B1）
-- ============================================================================

/--
`g_p(t) := vertical σ t * log p` の `t` 微分。

`vertical σ t = σ + i t` なので `d/dt` は `i`、
よって `g_p` の導関数は `i * log p` になる。
-/
lemma hasDerivAt_vertical_mul_log_p
    (p : ℕ) (σ t : ℝ) :
    HasDerivAt
      (fun u : ℝ => vertical σ u * (Real.log (p : ℝ) : ℂ))
      (Complex.I * (Real.log (p : ℝ) : ℂ)) t := by
  have hvertical : HasDerivAt (fun u : ℝ => vertical σ u) Complex.I t := by
    simpa [vertical, one_mul] using
      ((((hasDerivAt_id (t : ℂ)).mul_const Complex.I).comp_ofReal).const_add (σ : ℂ))
  simpa [mul_assoc] using hvertical.mul_const (Real.log (p : ℝ) : ℂ)

/--
`w_p(t) = exp((σ+it)log p) - 1` の `t` 微分。

連鎖律より
`w_p'(t) = exp((σ+it)log p) * (i * log p)`。
-/
lemma hasDerivAt_eulerZeta_exp_s_log_p_sub_one
    (p : ℕ) (σ t : ℝ) :
    HasDerivAt
      (fun u : ℝ => eulerZeta_exp_s_log_p_sub_one p σ u)
      (Complex.exp (vertical σ t * (Real.log (p : ℝ) : ℂ)) *
        (Complex.I * (Real.log (p : ℝ) : ℂ))) t := by
  unfold eulerZeta_exp_s_log_p_sub_one
  have hinner :=
    hasDerivAt_vertical_mul_log_p (p := p) (σ := σ) (t := t)
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    ((Complex.hasDerivAt_exp
      (vertical σ t * (Real.log (p : ℝ) : ℂ))).comp t hinner).sub_const (1 : ℂ)

/--
`w_p` の導関数の `deriv` 版。
-/
lemma deriv_eulerZeta_exp_s_log_p_sub_one
    (p : ℕ) (σ t : ℝ) :
    deriv (fun u : ℝ => eulerZeta_exp_s_log_p_sub_one p σ u) t =
      Complex.exp (vertical σ t * (Real.log (p : ℝ) : ℂ)) *
        (Complex.I * (Real.log (p : ℝ) : ℂ)) :=
  (hasDerivAt_eulerZeta_exp_s_log_p_sub_one (p := p) (σ := σ) (t := t)).deriv

/--
`w_p` に対する位相速度の明示式。

`phaseVel f t = Im(f'(t)/f(t))` に `f = w_p` を代入した形。
-/
lemma phaseVel_eulerZeta_exp_s_log_p_sub_one_eq
    (p : ℕ) (σ t : ℝ) :
    DkMath.RH.phaseVel (fun u : ℝ => eulerZeta_exp_s_log_p_sub_one p σ u) t =
      (((Complex.exp (vertical σ t * (Real.log (p : ℝ) : ℂ)) *
          (Complex.I * (Real.log (p : ℝ) : ℂ))) /
        (eulerZeta_exp_s_log_p_sub_one p σ t)).im) := by
  simp [DkMath.RH.phaseVel, deriv_eulerZeta_exp_s_log_p_sub_one]

/--
`w_p(t) ≠ 0` の下で、`driftFreeAt` と `phaseVel = 0` は同値。

HOPC-RH では停留条件の入口として使う。
-/
lemma driftFreeAt_eulerZeta_exp_s_log_p_sub_one_iff_phaseVel_eq_zero
    (p : ℕ) (σ t : ℝ)
    (hw_ne : eulerZeta_exp_s_log_p_sub_one p σ t ≠ 0) :
    DkMath.RH.driftFreeAt (fun u : ℝ => eulerZeta_exp_s_log_p_sub_one p σ u) t ↔
      DkMath.RH.phaseVel (fun u : ℝ => eulerZeta_exp_s_log_p_sub_one p σ u) t = 0 := by
  simpa using
    (DkMath.RH.driftFreeAt_iff_phaseVel_eq_zero
      (f := fun u : ℝ => eulerZeta_exp_s_log_p_sub_one p σ u)
      (t := t) hw_ne)

-- ============================================================================
-- 12. HOPC-RH: 単一素数因子 `w_p` の 2 次情報（RH-C1）
-- ============================================================================

/--
`w_p` の 2 階導関数（`t` 方向）。

`w_p'(t) = exp(g(t)) * c`（`c = i*log p`）なので、
再度の連鎖律により `w_p''(t) = exp(g(t)) * c * c`。
-/
lemma hasDerivAt_deriv_eulerZeta_exp_s_log_p_sub_one
    (p : ℕ) (σ t : ℝ) :
    HasDerivAt
      (fun u : ℝ => deriv (fun v : ℝ => eulerZeta_exp_s_log_p_sub_one p σ v) u)
      (Complex.exp (vertical σ t * (Real.log (p : ℝ) : ℂ)) *
        (Complex.I * (Real.log (p : ℝ) : ℂ)) *
        (Complex.I * (Real.log (p : ℝ) : ℂ))) t := by
  let lp : ℂ := (Real.log (p : ℝ) : ℂ)
  have h_deriv_fun :
      (fun u : ℝ => deriv (fun v : ℝ => eulerZeta_exp_s_log_p_sub_one p σ v) u) =
      (fun u : ℝ => Complex.exp (vertical σ u * lp) * (Complex.I * lp)) := by
    funext u
    simpa [lp] using deriv_eulerZeta_exp_s_log_p_sub_one (p := p) (σ := σ) (t := u)
  rw [h_deriv_fun]
  have hinner := hasDerivAt_vertical_mul_log_p (p := p) (σ := σ) (t := t)
  have hexp :
      HasDerivAt
        (fun u : ℝ => Complex.exp (vertical σ u * lp))
        (Complex.exp (vertical σ t * lp) * (Complex.I * lp)) t := by
    simpa [lp] using
      (Complex.hasDerivAt_exp (vertical σ t * lp)).comp t hinner
  have hmul := hexp.mul_const (Complex.I * lp)
  simpa [lp, mul_assoc] using hmul

/--
`w_p` の 2 階導関数の `deriv` 版。
-/
lemma deriv_deriv_eulerZeta_exp_s_log_p_sub_one
    (p : ℕ) (σ t : ℝ) :
    deriv (fun u : ℝ => deriv (fun v : ℝ => eulerZeta_exp_s_log_p_sub_one p σ v) u) t =
      Complex.exp (vertical σ t * (Real.log (p : ℝ) : ℂ)) *
        (Complex.I * (Real.log (p : ℝ) : ℂ)) *
        (Complex.I * (Real.log (p : ℝ) : ℂ)) :=
  (hasDerivAt_deriv_eulerZeta_exp_s_log_p_sub_one (p := p) (σ := σ) (t := t)).deriv

/--
`w_p(t) ≠ 0` の下で、`stationaryAt` は `driftFreeAt` と同値。
-/
lemma stationaryAt_eulerZeta_exp_s_log_p_sub_one_iff_driftFreeAt
    (p : ℕ) (σ t : ℝ)
    (hw_ne : eulerZeta_exp_s_log_p_sub_one p σ t ≠ 0) :
    DkMath.RH.stationaryAt (fun u : ℝ => eulerZeta_exp_s_log_p_sub_one p σ u) t ↔
      DkMath.RH.driftFreeAt (fun u : ℝ => eulerZeta_exp_s_log_p_sub_one p σ u) t := by
  simpa [Iff.comm] using
    (DkMath.RH.driftFreeAt_iff_stationaryAt
      (f := fun u : ℝ => eulerZeta_exp_s_log_p_sub_one p σ u)
      (t := t) hw_ne)

/--
`w_p(t) ≠ 0` の下で、非退化停留点は
`driftFreeAt ∧ phaseCurv ≠ 0` と同値。
-/
lemma nondegenerateStationaryAt_eulerZeta_exp_s_log_p_sub_one_iff
    (p : ℕ) (σ t : ℝ)
    (hw_ne : eulerZeta_exp_s_log_p_sub_one p σ t ≠ 0) :
    DkMath.RH.nondegenerateStationaryAt
        (fun u : ℝ => eulerZeta_exp_s_log_p_sub_one p σ u) t
      ↔
    (DkMath.RH.driftFreeAt (fun u : ℝ => eulerZeta_exp_s_log_p_sub_one p σ u) t ∧
      DkMath.RH.phaseCurv (fun u : ℝ => eulerZeta_exp_s_log_p_sub_one p σ u) t ≠ 0) := by
  simpa using
    (DkMath.RH.nondegenerateStationaryAt_iff_driftFreeAt_and_phaseCurv_ne_zero
      (f := fun u : ℝ => eulerZeta_exp_s_log_p_sub_one p σ u)
      (t := t) hw_ne)

-- ============================================================================
-- 13. HOPC-RH: 有限 Euler 積観測量 API（RH-D1）
-- ============================================================================

/-- 空集合での有限 Euler 積（複素版）は 1。 -/
@[simp] lemma eulerZetaFinite_empty (s : ℂ) :
    eulerZetaFinite (S := (∅ : Finset {p // Nat.Prime p})) s = 1 := by
  simp [eulerZetaFinite]

/-- `insert` による有限 Euler 積（複素版）の再帰展開。 -/
lemma eulerZetaFinite_insert
    (p : {p // Nat.Prime p}) (S : Finset {p // Nat.Prime p}) (s : ℂ)
    (hp : p ∉ S) :
    eulerZetaFinite (S := insert p S) s =
      eulerZetaFactor p.1 s * eulerZetaFinite (S := S) s := by
  simp [eulerZetaFinite, hp]

/-- 空集合での有限 Euler 積（magnitude 版）は 1。 -/
@[simp] lemma eulerZetaMagFinite_empty (σ t : ℝ) :
    eulerZetaMagFinite (S := (∅ : Finset {p // Nat.Prime p})) σ t = 1 := by
  simp [eulerZetaMagFinite]

/-- `insert` による有限 Euler 積（magnitude 版）の再帰展開。 -/
lemma eulerZetaMagFinite_insert
    (p : {p // Nat.Prime p}) (S : Finset {p // Nat.Prime p}) (σ t : ℝ)
    (hp : p ∉ S) :
    eulerZetaMagFinite (S := insert p S) σ t =
      eulerZetaFactorMag p.1 σ t * eulerZetaMagFinite (S := S) σ t := by
  simp [eulerZetaMagFinite, hp]

/-- 空集合での有限位相速度和は 0。 -/
@[simp] lemma eulerZetaPhaseVelFinite_empty (σ t : ℝ) :
    eulerZetaPhaseVelFinite (S := (∅ : Finset {p // Nat.Prime p})) σ t = 0 := by
  simp [eulerZetaPhaseVelFinite]

/-- `insert` による有限位相速度和の再帰展開。 -/
lemma eulerZetaPhaseVelFinite_insert
    (p : {p // Nat.Prime p}) (S : Finset {p // Nat.Prime p}) (σ t : ℝ)
    (hp : p ∉ S) :
    eulerZetaPhaseVelFinite (S := insert p S) σ t =
      eulerZetaPhaseVelLocal p.1 σ t + eulerZetaPhaseVelFinite (S := S) σ t := by
  simp [eulerZetaPhaseVelFinite, hp]

/-- 局所位相速度寄与は `phaseVel` 明示式補題と一致する。 -/
lemma eulerZetaPhaseVelLocal_eq_phaseVel_formula
    (p : ℕ) (σ t : ℝ) :
    eulerZetaPhaseVelLocal p σ t =
      (((Complex.exp (vertical σ t * (Real.log (p : ℝ) : ℂ)) *
          (Complex.I * (Real.log (p : ℝ) : ℂ))) /
        (eulerZeta_exp_s_log_p_sub_one p σ t)).im) := by
  simpa [eulerZetaPhaseVelLocal] using
    (phaseVel_eulerZeta_exp_s_log_p_sub_one_eq (p := p) (σ := σ) (t := t))

-- ============================================================================
-- 14. HOPC-RH: 有限積の位相速度を局所寄与和へ落とす（RH-D2）
-- ============================================================================

/-- 空集合での `w_p` 有限積は 1。 -/
@[simp] lemma eulerZetaExpSubOneFinite_empty (σ t : ℝ) :
    eulerZetaExpSubOneFinite (S := (∅ : Finset {p // Nat.Prime p})) σ t = 1 := by
  simp [eulerZetaExpSubOneFinite]

/-- `insert` による `w_p` 有限積の再帰展開。 -/
lemma eulerZetaExpSubOneFinite_insert
    (p : {p // Nat.Prime p}) (S : Finset {p // Nat.Prime p}) (σ t : ℝ)
    (hp : p ∉ S) :
    eulerZetaExpSubOneFinite (S := insert p S) σ t =
      eulerZeta_exp_s_log_p_sub_one p.1 σ t *
        eulerZetaExpSubOneFinite (S := S) σ t := by
  simp [eulerZetaExpSubOneFinite, hp]

/-- `w_p` 有限積は各点で微分可能。 -/
lemma differentiableAt_eulerZetaExpSubOneFinite
    (S : Finset {p // Nat.Prime p}) (σ t : ℝ) :
    DifferentiableAt ℝ (fun u : ℝ => eulerZetaExpSubOneFinite S σ u) t := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp [eulerZetaExpSubOneFinite]
  | @insert p S hp ih =>
      have hd_p :
          DifferentiableAt ℝ (fun u : ℝ => eulerZeta_exp_s_log_p_sub_one p.1 σ u) t :=
        (hasDerivAt_eulerZeta_exp_s_log_p_sub_one (p := p.1) (σ := σ) (t := t)).differentiableAt
      simpa [eulerZetaExpSubOneFinite, hp] using hd_p.mul ih

/--
`insert` 1ステップ版の積→和補題。

`w_p` 有限積で 0 除算が起きない点では、位相速度は 1 因子ぶん加法分解できる。
-/
lemma phaseVel_eulerZetaExpSubOneFinite_insert
    (p : {p // Nat.Prime p}) (S : Finset {p // Nat.Prime p}) (σ t : ℝ)
    (hp : p ∉ S)
    (hp_ne : eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hS_ne : eulerZetaExpSubOneFinite (S := S) σ t ≠ 0) :
    DkMath.RH.phaseVel
        (fun u : ℝ => eulerZetaExpSubOneFinite (S := insert p S) σ u) t =
      eulerZetaPhaseVelLocal p.1 σ t +
        DkMath.RH.phaseVel (fun u : ℝ => eulerZetaExpSubOneFinite (S := S) σ u) t := by
  have hmul :
      (fun u : ℝ => eulerZetaExpSubOneFinite (S := insert p S) σ u) =
      (fun u : ℝ =>
        eulerZeta_exp_s_log_p_sub_one p.1 σ u * eulerZetaExpSubOneFinite (S := S) σ u) := by
    funext u
    simp [eulerZetaExpSubOneFinite, hp]
  rw [hmul]
  have hd_p :
      DifferentiableAt ℝ (fun u : ℝ => eulerZeta_exp_s_log_p_sub_one p.1 σ u) t :=
    (hasDerivAt_eulerZeta_exp_s_log_p_sub_one (p := p.1) (σ := σ) (t := t)).differentiableAt
  have hd_S :
      DifferentiableAt ℝ (fun u : ℝ => eulerZetaExpSubOneFinite (S := S) σ u) t :=
    differentiableAt_eulerZetaExpSubOneFinite (S := S) (σ := σ) (t := t)
  simpa [eulerZetaPhaseVelLocal] using
    (DkMath.RH.phaseVel_mul
      (f := fun u : ℝ => eulerZeta_exp_s_log_p_sub_one p.1 σ u)
      (g := fun u : ℝ => eulerZetaExpSubOneFinite (S := S) σ u)
      (t := t) hd_p hd_S hp_ne hS_ne)

/-- `S` 上で `w_p(t) ≠ 0` なら、その有限積も非零。 -/
lemma eulerZetaExpSubOneFinite_ne_zero_of_ne
    (S : Finset {p // Nat.Prime p}) (σ t : ℝ)
    (hS_ne : ∀ p ∈ S, eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0) :
    eulerZetaExpSubOneFinite (S := S) σ t ≠ 0 := by
  unfold eulerZetaExpSubOneFinite
  exact (Finset.prod_ne_zero_iff).2 (by
    intro p hp
    exact hS_ne p hp)

/--
有限積版の積→和補題（本体）。

`S` 内の各素数因子で `w_p(t) ≠ 0` が成り立つとき、
`w_p` 有限積の位相速度は局所位相速度寄与の有限和に一致する。
-/
lemma phaseVel_eulerZetaExpSubOneFinite_eq_sum
    (S : Finset {p // Nat.Prime p}) (σ t : ℝ)
    (hS_ne :
      ∀ p ∈ S, eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0) :
    DkMath.RH.phaseVel (fun u : ℝ => eulerZetaExpSubOneFinite (S := S) σ u) t =
      eulerZetaPhaseVelFinite (S := S) σ t := by
  classical
  revert hS_ne
  refine Finset.induction_on S ?h0 ?hstep
  · intro _
    simp [eulerZetaExpSubOneFinite, eulerZetaPhaseVelFinite, DkMath.RH.phaseVel]
  · intro p S hp ih hS_ne
    have hp_ne : eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0 :=
      hS_ne p (Finset.mem_insert_self p S)
    have hS_ne' : ∀ q ∈ S, eulerZeta_exp_s_log_p_sub_one q.1 σ t ≠ 0 := by
      intro q hq
      exact hS_ne q (Finset.mem_insert_of_mem hq)
    have hprod_ne :
        eulerZetaExpSubOneFinite (S := S) σ t ≠ 0 := by
      exact eulerZetaExpSubOneFinite_ne_zero_of_ne
        (S := S) (σ := σ) (t := t) hS_ne'
    have h_insert :=
      phaseVel_eulerZetaExpSubOneFinite_insert
        (p := p) (S := S) (σ := σ) (t := t) hp hp_ne hprod_ne
    calc
      DkMath.RH.phaseVel
          (fun u : ℝ => eulerZetaExpSubOneFinite (S := insert p S) σ u) t
          = eulerZetaPhaseVelLocal p.1 σ t +
              DkMath.RH.phaseVel (fun u : ℝ => eulerZetaExpSubOneFinite (S := S) σ u) t := h_insert
      _ = eulerZetaPhaseVelLocal p.1 σ t + eulerZetaPhaseVelFinite (S := S) σ t := by
          rw [ih hS_ne']
      _ = eulerZetaPhaseVelFinite (S := insert p S) σ t := by
          symm
          exact eulerZetaPhaseVelFinite_insert (p := p) (S := S) (σ := σ) (t := t) hp

-- ============================================================================
-- 15. RH-E1: exp 形 Euler 因子の位相速度接続
-- ============================================================================

/-- exp 形 Euler 因子の有限積：空集合は 1。 -/
@[simp] lemma eulerZetaFactorVerticalExpFinite_empty (σ t : ℝ) :
    eulerZetaFactorVerticalExpFinite (S := (∅ : Finset {p // Nat.Prime p})) σ t = 1 := by
  simp [eulerZetaFactorVerticalExpFinite]

/-- exp 形 Euler 因子の有限積：`insert` 展開。 -/
lemma eulerZetaFactorVerticalExpFinite_insert
    (p : {p // Nat.Prime p}) (S : Finset {p // Nat.Prime p}) (σ t : ℝ)
    (hp : p ∉ S) :
    eulerZetaFactorVerticalExpFinite (S := insert p S) σ t =
      eulerZetaFactorVerticalExp p.1 σ t *
        eulerZetaFactorVerticalExpFinite (S := S) σ t := by
  simp [eulerZetaFactorVerticalExpFinite, hp]

/-- 局所因子 `exp / (exp-1)` は分母非零なら非零。 -/
lemma eulerZetaFactorVerticalExp_ne_zero
    (p : ℕ) (σ t : ℝ)
    (hw_ne : eulerZeta_exp_s_log_p_sub_one p σ t ≠ 0) :
    eulerZetaFactorVerticalExp p σ t ≠ 0 := by
  unfold eulerZetaFactorVerticalExp
  exact div_ne_zero (Complex.exp_ne_zero _) hw_ne

/-- `S` 上で `w_p(t) ≠ 0` なら、exp 形 Euler 因子有限積は非零。 -/
lemma eulerZetaFactorVerticalExpFinite_ne_zero_of_ne
    (S : Finset {p // Nat.Prime p}) (σ t : ℝ)
    (hS_ne : ∀ p ∈ S, eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0) :
    eulerZetaFactorVerticalExpFinite (S := S) σ t ≠ 0 := by
  unfold eulerZetaFactorVerticalExpFinite
  exact (Finset.prod_ne_zero_iff).2 (by
    intro p hp
    exact eulerZetaFactorVerticalExp_ne_zero
      (p := p.1) (σ := σ) (t := t) (hS_ne p hp))

/-- `exp((σ+it)log p)` の位相速度は `log p`。 -/
lemma phaseVel_exp_vertical_mul_log_p_eq_log
    (p : ℕ) (σ t : ℝ) :
    DkMath.RH.phaseVel
      (fun u : ℝ => Complex.exp (vertical σ u * (Real.log (p : ℝ) : ℂ))) t
      = Real.log (p : ℝ) := by
  have hinner := hasDerivAt_vertical_mul_log_p (p := p) (σ := σ) (t := t)
  have hderiv :
      deriv (fun u : ℝ => Complex.exp (vertical σ u * (Real.log (p : ℝ) : ℂ))) t =
        Complex.exp (vertical σ t * (Real.log (p : ℝ) : ℂ)) *
          (Complex.I * (Real.log (p : ℝ) : ℂ)) := by
    simpa using ((Complex.hasDerivAt_exp
      (vertical σ t * (Real.log (p : ℝ) : ℂ))).comp t hinner).deriv
  unfold DkMath.RH.phaseVel
  rw [hderiv]
  have hexp_ne : Complex.exp (vertical σ t * (Real.log (p : ℝ) : ℂ)) ≠ 0 :=
    Complex.exp_ne_zero _
  have hcancel :
      (((Complex.exp (vertical σ t * (Real.log (p : ℝ) : ℂ)) *
          (Complex.I * (Real.log (p : ℝ) : ℂ))) /
        Complex.exp (vertical σ t * (Real.log (p : ℝ) : ℂ))).im) =
      (Complex.I * (Real.log (p : ℝ) : ℂ)).im := by
    field_simp [hexp_ne]
  rw [hcancel]
  simpa using (Complex.log_ofReal_re (p : ℝ))

/-- 分母非零の下で exp 形 Euler 因子は微分可能。 -/
lemma differentiableAt_eulerZetaFactorVerticalExp_of_ne
    (p : ℕ) (σ t : ℝ)
    (hw_ne : eulerZeta_exp_s_log_p_sub_one p σ t ≠ 0) :
    DifferentiableAt ℝ (fun u : ℝ => eulerZetaFactorVerticalExp p σ u) t := by
  unfold eulerZetaFactorVerticalExp
  have hnum :
      DifferentiableAt ℝ
        (fun u : ℝ => Complex.exp (vertical σ u * (Real.log (p : ℝ) : ℂ))) t := by
    have hinner := hasDerivAt_vertical_mul_log_p (p := p) (σ := σ) (t := t)
    exact ((Complex.hasDerivAt_exp
      (vertical σ t * (Real.log (p : ℝ) : ℂ))).comp t hinner).differentiableAt
  have hden :
      DifferentiableAt ℝ (fun u : ℝ => eulerZeta_exp_s_log_p_sub_one p σ u) t :=
    (hasDerivAt_eulerZeta_exp_s_log_p_sub_one (p := p) (σ := σ) (t := t)).differentiableAt
  exact hnum.div hden hw_ne

/--
exp 形 Euler 因子の局所位相速度は
`log p - phaseVel(w_p)`。
-/
lemma phaseVel_eulerZetaFactorVerticalExp_eq_log_sub_phaseVelLocal
    (p : ℕ) (σ t : ℝ)
    (hw_ne : eulerZeta_exp_s_log_p_sub_one p σ t ≠ 0) :
    eulerZetaFactorPhaseVelLocal p σ t =
      Real.log (p : ℝ) - eulerZetaPhaseVelLocal p σ t := by
  unfold eulerZetaFactorPhaseVelLocal eulerZetaFactorVerticalExp eulerZetaPhaseVelLocal
  have hnum :
      DifferentiableAt ℝ
        (fun u : ℝ => Complex.exp (vertical σ u * (Real.log (p : ℝ) : ℂ))) t := by
    have hinner := hasDerivAt_vertical_mul_log_p (p := p) (σ := σ) (t := t)
    exact ((Complex.hasDerivAt_exp
      (vertical σ t * (Real.log (p : ℝ) : ℂ))).comp t hinner).differentiableAt
  have hden :
      DifferentiableAt ℝ (fun u : ℝ => eulerZeta_exp_s_log_p_sub_one p σ u) t :=
    (hasDerivAt_eulerZeta_exp_s_log_p_sub_one (p := p) (σ := σ) (t := t)).differentiableAt
  have hnum_ne :
      Complex.exp (vertical σ t * (Real.log (p : ℝ) : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  calc
    DkMath.RH.phaseVel
        (fun u : ℝ =>
          Complex.exp (vertical σ u * (Real.log (p : ℝ) : ℂ)) /
            eulerZeta_exp_s_log_p_sub_one p σ u) t
        = DkMath.RH.phaseVel
            (fun u : ℝ => Complex.exp (vertical σ u * (Real.log (p : ℝ) : ℂ))) t
          - DkMath.RH.phaseVel (fun u : ℝ => eulerZeta_exp_s_log_p_sub_one p σ u) t := by
              exact DkMath.RH.phaseVel_div
                (f := fun u : ℝ => Complex.exp (vertical σ u * (Real.log (p : ℝ) : ℂ)))
                (g := fun u : ℝ => eulerZeta_exp_s_log_p_sub_one p σ u)
                (t := t) hnum hden hnum_ne hw_ne
    _ = Real.log (p : ℝ) -
          DkMath.RH.phaseVel (fun u : ℝ => eulerZeta_exp_s_log_p_sub_one p σ u) t := by
          rw [phaseVel_exp_vertical_mul_log_p_eq_log (p := p) (σ := σ) (t := t)]

/-- 分母非零条件の下で exp 形 Euler 因子有限積は微分可能。 -/
lemma differentiableAt_eulerZetaFactorVerticalExpFinite_of_ne
    (S : Finset {p // Nat.Prime p}) (σ t : ℝ)
    (hS_ne : ∀ p ∈ S, eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0) :
    DifferentiableAt ℝ (fun u : ℝ => eulerZetaFactorVerticalExpFinite (S := S) σ u) t := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp [eulerZetaFactorVerticalExpFinite]
  | @insert p S hp ih =>
      have hp_ne : eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0 :=
        hS_ne p (Finset.mem_insert_self p S)
      have hS_ne' : ∀ q ∈ S, eulerZeta_exp_s_log_p_sub_one q.1 σ t ≠ 0 := by
        intro q hq
        exact hS_ne q (Finset.mem_insert_of_mem hq)
      have hd_p :
          DifferentiableAt ℝ (fun u : ℝ => eulerZetaFactorVerticalExp p.1 σ u) t :=
        differentiableAt_eulerZetaFactorVerticalExp_of_ne (p := p.1) (σ := σ) (t := t) hp_ne
      have hd_S :
          DifferentiableAt ℝ (fun u : ℝ => eulerZetaFactorVerticalExpFinite (S := S) σ u) t :=
        ih hS_ne'
      simpa [eulerZetaFactorVerticalExpFinite, hp] using hd_p.mul hd_S

/--
exp 形 Euler 因子有限積の位相速度は、局所位相速度寄与の有限和に一致する。
-/
lemma phaseVel_eulerZetaFactorVerticalExpFinite_eq_sum
    (S : Finset {p // Nat.Prime p}) (σ t : ℝ)
    (hS_ne :
      ∀ p ∈ S, eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0) :
    DkMath.RH.phaseVel (fun u : ℝ => eulerZetaFactorVerticalExpFinite (S := S) σ u) t =
      eulerZetaFactorPhaseVelFinite (S := S) σ t := by
  classical
  revert hS_ne
  refine Finset.induction_on S ?h0 ?hstep
  · intro _
    simp [eulerZetaFactorVerticalExpFinite, eulerZetaFactorPhaseVelFinite, DkMath.RH.phaseVel]
  · intro p S hp ih hS_ne
    have hp_ne : eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0 :=
      hS_ne p (Finset.mem_insert_self p S)
    have hS_ne' : ∀ q ∈ S, eulerZeta_exp_s_log_p_sub_one q.1 σ t ≠ 0 := by
      intro q hq
      exact hS_ne q (Finset.mem_insert_of_mem hq)
    have hprod_ne :
        eulerZetaFactorVerticalExpFinite (S := S) σ t ≠ 0 := by
      exact eulerZetaFactorVerticalExpFinite_ne_zero_of_ne
        (S := S) (σ := σ) (t := t) hS_ne'
    have hmul :
      (fun u : ℝ => eulerZetaFactorVerticalExpFinite (S := insert p S) σ u) =
      (fun u : ℝ => eulerZetaFactorVerticalExp p.1 σ u *
        eulerZetaFactorVerticalExpFinite (S := S) σ u) := by
      funext u
      simp [eulerZetaFactorVerticalExpFinite, hp]
    rw [hmul]
    have hd_p :
        DifferentiableAt ℝ (fun u : ℝ => eulerZetaFactorVerticalExp p.1 σ u) t :=
      differentiableAt_eulerZetaFactorVerticalExp_of_ne (p := p.1) (σ := σ) (t := t) hp_ne
    have hd_S :
        DifferentiableAt ℝ (fun u : ℝ => eulerZetaFactorVerticalExpFinite (S := S) σ u) t := by
      exact differentiableAt_eulerZetaFactorVerticalExpFinite_of_ne
        (S := S) (σ := σ) (t := t) hS_ne'
    have hp_factor_ne :
        eulerZetaFactorVerticalExp p.1 σ t ≠ 0 :=
      eulerZetaFactorVerticalExp_ne_zero (p := p.1) (σ := σ) (t := t) hp_ne
    have hstep_mul :
        DkMath.RH.phaseVel
          (fun u : ℝ =>
            eulerZetaFactorVerticalExp p.1 σ u *
              eulerZetaFactorVerticalExpFinite (S := S) σ u) t
          =
        eulerZetaFactorPhaseVelLocal p.1 σ t +
          DkMath.RH.phaseVel (fun u : ℝ => eulerZetaFactorVerticalExpFinite (S := S) σ u) t := by
      simpa [eulerZetaFactorPhaseVelLocal] using
        (DkMath.RH.phaseVel_mul
          (f := fun u : ℝ => eulerZetaFactorVerticalExp p.1 σ u)
          (g := fun u : ℝ => eulerZetaFactorVerticalExpFinite (S := S) σ u)
          (t := t) hd_p hd_S hp_factor_ne hprod_ne)
    calc
      DkMath.RH.phaseVel
          (fun u : ℝ =>
            eulerZetaFactorVerticalExp p.1 σ u *
              eulerZetaFactorVerticalExpFinite (S := S) σ u) t
          = eulerZetaFactorPhaseVelLocal p.1 σ t +
              DkMath.RH.phaseVel (fun u : ℝ => eulerZetaFactorVerticalExpFinite (S := S) σ u) t :=
            hstep_mul
      _ = eulerZetaFactorPhaseVelLocal p.1 σ t +
            eulerZetaFactorPhaseVelFinite (S := S) σ t := by
              rw [ih hS_ne']
      _ = eulerZetaFactorPhaseVelFinite (S := insert p S) σ t := by
            symm
            simp [eulerZetaFactorPhaseVelFinite, hp]

-- ============================================================================
-- 16. RH-E2: eulerZetaFinite 本体への接続
-- ============================================================================

/-- 素数 `p` では `eulerZetaFactor (vertical σ t)` は exp 形表示に一致する。 -/
lemma eulerZetaFactor_onVertical_eq_factorVerticalExp
    (p : {p // Nat.Prime p}) (σ t : ℝ) :
    eulerZetaFactor p.1 (vertical σ t) = eulerZetaFactorVerticalExp p.1 σ t := by
  have hp0 : (p.1 : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.Prime.ne_zero p.2)
  rw [eulerZetaFactor, eulerZetaFactorVerticalExp, eulerZeta_exp_s_log_p_sub_one]
  rw [Complex.cpow_def_of_ne_zero hp0]
  rw [Complex.natCast_log]
  simp [mul_comm]

/-- 有限 Euler 積の縦線版は exp 形因子の有限積に一致する。 -/
lemma eulerZetaFinite_onVertical_eq_factorVerticalExpFinite
    (S : Finset {p // Nat.Prime p}) (σ t : ℝ) :
    eulerZetaFinite_onVertical S σ t = eulerZetaFactorVerticalExpFinite (S := S) σ t := by
  unfold eulerZetaFinite_onVertical eulerZetaFinite eulerZetaFactorVerticalExpFinite
  refine Finset.prod_congr rfl ?_
  intro p hp
  exact eulerZetaFactor_onVertical_eq_factorVerticalExp (p := p) (σ := σ) (t := t)

/--
`eulerZetaFinite_onVertical` の位相速度は、exp 形局所寄与の有限和へ落ちる。
-/
lemma phaseVel_eulerZetaFinite_onVertical_eq_factor_sum
    (S : Finset {p // Nat.Prime p}) (σ t : ℝ)
    (hS_ne :
      ∀ p ∈ S, eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0) :
    DkMath.RH.phaseVel (fun u : ℝ => eulerZetaFinite_onVertical S σ u) t =
      eulerZetaFactorPhaseVelFinite (S := S) σ t := by
  have hfun :
      (fun u : ℝ => eulerZetaFinite_onVertical S σ u) =
      (fun u : ℝ => eulerZetaFactorVerticalExpFinite (S := S) σ u) := by
    funext u
    exact eulerZetaFinite_onVertical_eq_factorVerticalExpFinite (S := S) (σ := σ) (t := u)
  rw [hfun]
  exact phaseVel_eulerZetaFactorVerticalExpFinite_eq_sum (S := S) (σ := σ) (t := t) hS_ne

/-- `w_p(t) ≠ 0` が各素数で成り立てば、有限 Euler 積本体も `t` で非零。 -/
lemma eulerZetaFinite_onVertical_ne_zero_of_ne
    (S : Finset {p // Nat.Prime p}) (σ t : ℝ)
    (hS_ne : ∀ p ∈ S, eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0) :
    eulerZetaFinite_onVertical S σ t ≠ 0 := by
  rw [eulerZetaFinite_onVertical_eq_factorVerticalExpFinite (S := S) (σ := σ) (t := t)]
  exact eulerZetaFactorVerticalExpFinite_ne_zero_of_ne
    (S := S) (σ := σ) (t := t) hS_ne

/--
`eulerZetaFinite_onVertical` に対する停留同値。

`S` 内の全素数で `w_p(t) ≠ 0` の下、
`driftFreeAt` は `eulerZetaFactorPhaseVelFinite = 0` と同値。
-/
lemma driftFreeAt_eulerZetaFinite_onVertical_iff_factor_sum_eq_zero
    (S : Finset {p // Nat.Prime p}) (σ t : ℝ)
    (hS_ne : ∀ p ∈ S, eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0) :
    DkMath.RH.driftFreeAt (fun u : ℝ => eulerZetaFinite_onVertical S σ u) t ↔
      eulerZetaFactorPhaseVelFinite (S := S) σ t = 0 := by
  have hz :
      eulerZetaFinite_onVertical S σ t ≠ 0 :=
    eulerZetaFinite_onVertical_ne_zero_of_ne (S := S) (σ := σ) (t := t) hS_ne
  have hphase :
      DkMath.RH.phaseVel (fun u : ℝ => eulerZetaFinite_onVertical S σ u) t =
        eulerZetaFactorPhaseVelFinite (S := S) σ t :=
    phaseVel_eulerZetaFinite_onVertical_eq_factor_sum (S := S) (σ := σ) (t := t) hS_ne
  simpa [hphase] using
    (DkMath.RH.driftFreeAt_iff_phaseVel_eq_zero
      (f := fun u : ℝ => eulerZetaFinite_onVertical S σ u) (t := t) hz)

/--
`eulerZetaFinite_onVertical` の停留条件は有限局所寄与和の零化と同値。
-/
lemma stationaryAt_eulerZetaFinite_onVertical_iff_factor_sum_eq_zero
    (S : Finset {p // Nat.Prime p}) (σ t : ℝ)
    (hS_ne : ∀ p ∈ S, eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0) :
    DkMath.RH.stationaryAt (fun u : ℝ => eulerZetaFinite_onVertical S σ u) t ↔
      eulerZetaFactorPhaseVelFinite (S := S) σ t = 0 := by
  have hz :
      eulerZetaFinite_onVertical S σ t ≠ 0 :=
    eulerZetaFinite_onVertical_ne_zero_of_ne (S := S) (σ := σ) (t := t) hS_ne
  have hsd :
      DkMath.RH.stationaryAt (fun u : ℝ => eulerZetaFinite_onVertical S σ u) t ↔
        DkMath.RH.driftFreeAt (fun u : ℝ => eulerZetaFinite_onVertical S σ u) t := by
    symm
    exact DkMath.RH.driftFreeAt_iff_stationaryAt
      (f := fun u : ℝ => eulerZetaFinite_onVertical S σ u) (t := t) hz
  exact hsd.trans
    (driftFreeAt_eulerZetaFinite_onVertical_iff_factor_sum_eq_zero
      (S := S) (σ := σ) (t := t) hS_ne)

/--
`eulerZetaFinite_onVertical` の非退化停留条件。

停留（有限局所寄与和の零化）と位相曲率非零の組へ分解される。
-/
lemma nondegenerateStationaryAt_eulerZetaFinite_onVertical_iff
    (S : Finset {p // Nat.Prime p}) (σ t : ℝ)
    (hS_ne : ∀ p ∈ S, eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0) :
    DkMath.RH.nondegenerateStationaryAt (fun u : ℝ => eulerZetaFinite_onVertical S σ u) t
      ↔
      eulerZetaFactorPhaseVelFinite (S := S) σ t = 0 ∧
        DkMath.RH.phaseCurv (fun u : ℝ => eulerZetaFinite_onVertical S σ u) t ≠ 0 := by
  have hz :
      eulerZetaFinite_onVertical S σ t ≠ 0 :=
    eulerZetaFinite_onVertical_ne_zero_of_ne (S := S) (σ := σ) (t := t) hS_ne
  have hnd :
      DkMath.RH.nondegenerateStationaryAt (fun u : ℝ => eulerZetaFinite_onVertical S σ u) t ↔
        DkMath.RH.driftFreeAt (fun u : ℝ => eulerZetaFinite_onVertical S σ u) t ∧
          DkMath.RH.phaseCurv (fun u : ℝ => eulerZetaFinite_onVertical S σ u) t ≠ 0 :=
    DkMath.RH.nondegenerateStationaryAt_iff_driftFreeAt_and_phaseCurv_ne_zero
      (f := fun u : ℝ => eulerZetaFinite_onVertical S σ u) (t := t) hz
  constructor
  · intro h
    rcases hnd.mp h with ⟨hdrift, hcurv⟩
    exact ⟨(driftFreeAt_eulerZetaFinite_onVertical_iff_factor_sum_eq_zero
      (S := S) (σ := σ) (t := t) hS_ne).mp hdrift, hcurv⟩
  · intro h
    rcases h with ⟨hsum0, hcurv⟩
    exact hnd.mpr ⟨(driftFreeAt_eulerZetaFinite_onVertical_iff_factor_sum_eq_zero
      (S := S) (σ := σ) (t := t) hS_ne).mpr hsum0, hcurv⟩

/--
`eulerZetaFactorPhaseVelFinite` の明示式。

`S` 内で `w_p(t) ≠ 0` なら
`∑ phaseVel(factor_p) = ∑ (log p - phaseVel(w_p))`。
-/
lemma eulerZetaFactorPhaseVelFinite_eq_sum_log_sub_phaseVelLocal
    (S : Finset {p // Nat.Prime p}) (σ t : ℝ)
    (hS_ne : ∀ p ∈ S, eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0) :
    eulerZetaFactorPhaseVelFinite (S := S) σ t
      =
      ∑ p ∈ S, (Real.log (p.1 : ℝ) - eulerZetaPhaseVelLocal p.1 σ t) := by
  unfold eulerZetaFactorPhaseVelFinite
  refine Finset.sum_congr rfl ?_
  intro p hp
  exact phaseVel_eulerZetaFactorVerticalExp_eq_log_sub_phaseVelLocal
    (p := p.1) (σ := σ) (t := t) (hS_ne p hp)

/--
`eulerZetaFinite_onVertical` のドリフト消失条件（明示和版）。

`S` 内で `w_p(t) ≠ 0` なら、
`driftFreeAt` は `∑_{p∈S} (log p - phaseVel(w_p)) = 0` と同値。
-/
lemma driftFreeAt_eulerZetaFinite_onVertical_iff_sum_log_sub_phaseVelLocal_eq_zero
    (S : Finset {p // Nat.Prime p}) (σ t : ℝ)
    (hS_ne : ∀ p ∈ S, eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0) :
    DkMath.RH.driftFreeAt (fun u : ℝ => eulerZetaFinite_onVertical S σ u) t ↔
      (∑ p ∈ S, (Real.log (p.1 : ℝ) - eulerZetaPhaseVelLocal p.1 σ t)) = 0 := by
  rw [← eulerZetaFactorPhaseVelFinite_eq_sum_log_sub_phaseVelLocal
    (S := S) (σ := σ) (t := t) hS_ne]
  exact driftFreeAt_eulerZetaFinite_onVertical_iff_factor_sum_eq_zero
    (S := S) (σ := σ) (t := t) hS_ne

/--
`eulerZetaFinite_onVertical` の停留条件（明示和版）。

`S` 内で `w_p(t) ≠ 0` なら、
`stationaryAt` は `∑_{p∈S} (log p - phaseVel(w_p)) = 0` と同値。
-/
lemma stationaryAt_eulerZetaFinite_onVertical_iff_sum_log_sub_phaseVelLocal_eq_zero
    (S : Finset {p // Nat.Prime p}) (σ t : ℝ)
    (hS_ne : ∀ p ∈ S, eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0) :
    DkMath.RH.stationaryAt (fun u : ℝ => eulerZetaFinite_onVertical S σ u) t ↔
      (∑ p ∈ S, (Real.log (p.1 : ℝ) - eulerZetaPhaseVelLocal p.1 σ t)) = 0 := by
  rw [← eulerZetaFactorPhaseVelFinite_eq_sum_log_sub_phaseVelLocal
    (S := S) (σ := σ) (t := t) hS_ne]
  exact stationaryAt_eulerZetaFinite_onVertical_iff_factor_sum_eq_zero
    (S := S) (σ := σ) (t := t) hS_ne

/--
`eulerZetaFinite_onVertical` の非退化停留条件（明示和版）。

`S` 内で `w_p(t) ≠ 0` なら、
`nondegenerateStationaryAt` は
`(∑_{p∈S}(log p - phaseVel(w_p)) = 0) ∧ phaseCurv ≠ 0` と同値。
-/
lemma nondegenerateStationaryAt_eulerZetaFinite_onVertical_iff_sum_log_sub_phaseVelLocal
    (S : Finset {p // Nat.Prime p}) (σ t : ℝ)
    (hS_ne : ∀ p ∈ S, eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0) :
    DkMath.RH.nondegenerateStationaryAt (fun u : ℝ => eulerZetaFinite_onVertical S σ u) t
      ↔
      (∑ p ∈ S, (Real.log (p.1 : ℝ) - eulerZetaPhaseVelLocal p.1 σ t)) = 0 ∧
        DkMath.RH.phaseCurv (fun u : ℝ => eulerZetaFinite_onVertical S σ u) t ≠ 0 := by
  rw [← eulerZetaFactorPhaseVelFinite_eq_sum_log_sub_phaseVelLocal
    (S := S) (σ := σ) (t := t) hS_ne]
  exact nondegenerateStationaryAt_eulerZetaFinite_onVertical_iff
    (S := S) (σ := σ) (t := t) hS_ne

-- ============================================================================
-- 17. RH-H1: CFBRC 連携向け HOPC 公開インタフェース
-- ============================================================================

/-- HOPC 局所寄与は `log p - phaseVel(w_p)` に一致する。 -/
@[simp] lemma hopcPrimeLocalContribution_eq_log_sub_phaseVelLocal
    (p : ℕ) (σ t : ℝ) :
    hopcPrimeLocalContribution p σ t =
      Real.log (p : ℝ) - eulerZetaPhaseVelLocal p σ t := by
  rfl

/-- HOPC 寄与総和は `∑ (log p - phaseVel(w_p))` の別名。 -/
@[simp] lemma hopcPrimeContributionSum_eq_sum_log_sub_phaseVelLocal
    (S : Finset {p // Nat.Prime p}) (σ t : ℝ) :
    hopcPrimeContributionSum (S := S) σ t =
      ∑ p ∈ S, (Real.log (p.1 : ℝ) - eulerZetaPhaseVelLocal p.1 σ t) := by
  unfold hopcPrimeContributionSum hopcPrimeLocalContribution
  rfl

/--
HOPC 寄与総和と `eulerZetaFactorPhaseVelFinite` の同一化。
-/
lemma eulerZetaFactorPhaseVelFinite_eq_hopcPrimeContributionSum
    (S : Finset {p // Nat.Prime p}) (σ t : ℝ)
    (hS_ne : ∀ p ∈ S, eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0) :
    eulerZetaFactorPhaseVelFinite (S := S) σ t =
      hopcPrimeContributionSum (S := S) σ t := by
  rw [eulerZetaFactorPhaseVelFinite_eq_sum_log_sub_phaseVelLocal
    (S := S) (σ := σ) (t := t) hS_ne]
  simp

/--
`eulerZetaFinite_onVertical` のドリフト消失は HOPC 寄与総和 0 と同値。
-/
lemma driftFreeAt_eulerZetaFinite_onVertical_iff_hopcPrimeContributionSum_eq_zero
    (S : Finset {p // Nat.Prime p}) (σ t : ℝ)
    (hS_ne : ∀ p ∈ S, eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0) :
    DkMath.RH.driftFreeAt (fun u : ℝ => eulerZetaFinite_onVertical S σ u) t ↔
      hopcPrimeContributionSum (S := S) σ t = 0 := by
  rw [hopcPrimeContributionSum_eq_sum_log_sub_phaseVelLocal]
  exact driftFreeAt_eulerZetaFinite_onVertical_iff_sum_log_sub_phaseVelLocal_eq_zero
    (S := S) (σ := σ) (t := t) hS_ne

/--
`eulerZetaFinite_onVertical` の停留は HOPC 寄与総和 0 と同値。
-/
lemma stationaryAt_eulerZetaFinite_onVertical_iff_hopcPrimeContributionSum_eq_zero
    (S : Finset {p // Nat.Prime p}) (σ t : ℝ)
    (hS_ne : ∀ p ∈ S, eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0) :
    DkMath.RH.stationaryAt (fun u : ℝ => eulerZetaFinite_onVertical S σ u) t ↔
      hopcPrimeContributionSum (S := S) σ t = 0 := by
  rw [hopcPrimeContributionSum_eq_sum_log_sub_phaseVelLocal]
  exact stationaryAt_eulerZetaFinite_onVertical_iff_sum_log_sub_phaseVelLocal_eq_zero
    (S := S) (σ := σ) (t := t) hS_ne

/--
`eulerZetaFinite_onVertical` の非退化停留は
`hopcPrimeContributionSum = 0 ∧ phaseCurv ≠ 0` と同値。
-/
lemma nondegenerateStationaryAt_eulerZetaFinite_onVertical_iff_hopcPrimeContributionSum
    (S : Finset {p // Nat.Prime p}) (σ t : ℝ)
    (hS_ne : ∀ p ∈ S, eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0) :
    DkMath.RH.nondegenerateStationaryAt (fun u : ℝ => eulerZetaFinite_onVertical S σ u) t
      ↔
      hopcPrimeContributionSum (S := S) σ t = 0 ∧
        DkMath.RH.phaseCurv (fun u : ℝ => eulerZetaFinite_onVertical S σ u) t ≠ 0 := by
  rw [hopcPrimeContributionSum_eq_sum_log_sub_phaseVelLocal]
  exact nondegenerateStationaryAt_eulerZetaFinite_onVertical_iff_sum_log_sub_phaseVelLocal
    (S := S) (σ := σ) (t := t) hS_ne

/-- singleton 集合での `w_p ≠ 0` 前提供給 wrapper。 -/
lemma eulerZeta_exp_s_log_p_sub_one_ne_zero_on_singleton
    (p : {q // Nat.Prime q}) (σ t : ℝ)
    (hp_ne : eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0) :
    ∀ r ∈ ({p} : Finset {q // Nat.Prime q}),
      eulerZeta_exp_s_log_p_sub_one r.1 σ t ≠ 0 := by
  intro r hr
  have hrp : r = p := Finset.mem_singleton.mp hr
  simpa [hrp] using hp_ne

/-- singleton 集合では HOPC 寄与総和は局所寄与に簡約される。 -/
@[simp] lemma hopcPrimeContributionSum_singleton
    (p : {q // Nat.Prime q}) (σ t : ℝ) :
    hopcPrimeContributionSum (S := ({p} : Finset {q // Nat.Prime q})) σ t =
      hopcPrimeLocalContribution p.1 σ t := by
  simp [hopcPrimeContributionSum]

/--
singleton 観測器版の停留判定 wrapper（local 寄与ゼロ仮定）。

`w_p(σ,t) ≠ 0` と `hopcPrimeLocalContribution p σ t = 0` から
`stationaryAt` を得る。
-/
lemma stationaryAt_eulerZetaFinite_onVertical_singleton_of_hopcPrimeLocalContribution_eq_zero
    (p : {q // Nat.Prime q}) (σ t : ℝ)
    (hp_ne : eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0)
    (hlocal0 : hopcPrimeLocalContribution p.1 σ t = 0) :
    DkMath.RH.stationaryAt
      (fun v : ℝ => eulerZetaFinite_onVertical ({p} : Finset {q // Nat.Prime q}) σ v) t := by
  have hS_ne :
      ∀ r ∈ ({p} : Finset {q // Nat.Prime q}),
        eulerZeta_exp_s_log_p_sub_one r.1 σ t ≠ 0 :=
    eulerZeta_exp_s_log_p_sub_one_ne_zero_on_singleton (p := p) (σ := σ) (t := t) hp_ne
  exact
    (stationaryAt_eulerZetaFinite_onVertical_iff_hopcPrimeContributionSum_eq_zero
      (S := ({p} : Finset {q // Nat.Prime q})) (σ := σ) (t := t) hS_ne).2
      (by simpa using hlocal0)

end DkMath.RH.EulerZeta
