/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable

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

/-- σ > 1 のとき、exp((σ+it) log p) - 1 ≠ 0 -/
theorem eulerZeta_exp_s_log_p_sub_one_ne_zero_strong
    (p : ℕ) (hp : Nat.Prime p) (σ t : ℝ) (hσ : 1 < σ) :
    eulerZeta_exp_s_log_p_sub_one p σ t ≠ 0 := by
  -- 既存の補題を再利用
  exact eulerZeta_exp_s_log_p_sub_one_ne_zero p hp σ (lt_trans (by norm_num) hσ) t

/-- ‖eulerZetaFactorMag p σ t - 1‖ ≤ 2 / p^σ

   強い形の上界
-/
theorem eulerZetaFactorMag_norm_sub_one_upper_bound
    (p : ℕ) (hp : Nat.Prime p) (σ t : ℝ) (hσ : 1 < σ) :
    ‖eulerZetaFactorMag p σ t - 1‖ ≤ 2 / ((p : ℝ) ^ σ) := by
  have hσ0 : 0 < σ := lt_trans (by norm_num) hσ
  have hp2 : (2 : ℕ) ≤ p := Nat.Prime.two_le hp
  have hp_pos : 0 < (p : ℝ) := by
    have : (0 : ℕ) < p := lt_of_lt_of_le (by decide : (0:ℕ) < 2) hp2
    exact_mod_cast this
  have hlogp_pos : 0 < Real.log (p : ℝ) := by
    have hp1 : (1 : ℝ) < (p : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : (1:ℕ) < 2) hp2)
    exact Real.log_pos hp1
  let z : ℂ := vertical σ t * (Real.log (p : ℝ) : ℂ)
  let w : ℂ := Complex.exp z - 1
  let x : ℝ := Real.exp (σ * Real.log (p : ℝ))
  have hw_ne : w ≠ 0 :=
    eulerZeta_exp_s_log_p_sub_one_ne_zero_strong p hp σ t hσ
  have hw_norm_pos : 0 < ‖w‖ := (norm_pos_iff).2 hw_ne
  have hden_lower : x - 1 ≤ ‖w‖ := by
    have h := norm_sub_norm_le (Complex.exp z) (1 : ℂ)
    have : ‖Complex.exp z‖ = x := by
      calc
        ‖Complex.exp z‖ = Real.exp (z.re) := Complex.norm_exp _
        _ = Real.exp (σ * Real.log (p : ℝ)) := by
          have z_re := vertical_mul_log_p_re p σ t
          rw [z_re]
        _ = x := rfl
    rw [this] at h
    have : ‖(1 : ℂ)‖ = 1 := norm_one
    rw [this] at h
    have : ‖Complex.exp z - 1‖ = ‖w‖ := rfl
    rw [this] at h
    linarith
  have hx_rpow : x = (p : ℝ) ^ σ := by
    rw [Real.rpow_def_of_pos hp_pos]
    simp [x, mul_comm]
  have hx_ge_p : (p : ℝ) ≤ x := by
    have hσ1 : (1 : ℝ) ≤ σ := le_of_lt hσ
    have hlogp_nonneg : 0 ≤ Real.log (p : ℝ) := le_of_lt hlogp_pos
    have hmul : Real.log (p : ℝ) ≤ σ * Real.log (p : ℝ) := by
      calc Real.log (p : ℝ) = 1 * Real.log (p : ℝ) := by ring
        _ ≤ σ * Real.log (p : ℝ) := mul_le_mul_of_nonneg_right hσ1 hlogp_nonneg
    have hexp := Real.exp_le_exp.mpr hmul
    calc (p : ℝ) = Real.exp (Real.log (p : ℝ)) := (Real.exp_log hp_pos).symm
      _ ≤ Real.exp (σ * Real.log (p : ℝ)) := hexp
      _ = x := rfl
  have hx_ge_two : (2 : ℝ) ≤ x := by
    have hp2r : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    exact le_trans hp2r hx_ge_p
  have hx_gt_one : 1 < x := lt_of_lt_of_le (by norm_num) hx_ge_two
  have hx_m1_pos : 0 < x - 1 := sub_pos.mpr hx_gt_one
  have hgap : |x - ‖w‖| ≤ 1 := by
    have h := abs_norm_sub_norm_le (Complex.exp z) (Complex.exp z - 1)
    have h_norm_exp : ‖Complex.exp z‖ = x := by
      calc
        ‖Complex.exp z‖ = Real.exp (z.re) := Complex.norm_exp _
        _ = Real.exp (σ * Real.log (p : ℝ)) := by
          have z_re := vertical_mul_log_p_re p σ t
          rw [z_re]
        _ = x := rfl
    have h_norm_w : ‖Complex.exp z - 1‖ = ‖w‖ := rfl
    simpa [h_norm_exp, h_norm_w] using h
  have habs : |(x / ‖w‖) - 1| = |x - ‖w‖| / ‖w‖ := by
    have hw0 : ‖w‖ ≠ 0 := ne_of_gt hw_norm_pos
    calc
      |(x / ‖w‖) - 1|
          = |(x - ‖w‖) / ‖w‖| := by field_simp [hw0]
      _ = |x - ‖w‖| / |‖w‖| := abs_div (x - ‖w‖) ‖w‖
      _ = |x - ‖w‖| / ‖w‖ := by simp [abs_of_nonneg (norm_nonneg _)]
  have h1 : |x - ‖w‖| / ‖w‖ ≤ 1 / (x - 1) := by
    have hA : |x - ‖w‖| / ‖w‖ ≤ 1 / ‖w‖ :=
      div_le_div_of_nonneg_right hgap (le_of_lt hw_norm_pos)
    have hB : (1 : ℝ) / ‖w‖ ≤ 1 / (x - 1) :=
      one_div_le_one_div_of_le hx_m1_pos hden_lower
    exact le_trans hA hB
  have h2 : (1 : ℝ) / (x - 1) ≤ 2 / x := by
    -- 直接計算して差をとると整理しやすい。
    -- 2/x - 1/(x-1) = (x-2) / (x*(x-1)) であり、分子は非負、分母は正なので右辺は非負。
    have hx_pos : 0 < x := Real.exp_pos _
    have hx_ne : x ≠ 0 := by linarith [hx_ge_two]
    have hx_m1_ne : x - 1 ≠ 0 := by linarith [hx_gt_one]
    have hdiff : 2 / x - 1 / (x - 1) = (x - 2) / (x * (x - 1)) := by
      field_simp [hx_ne, hx_m1_ne]
      ring
    have hnum_nonneg : 0 ≤ x - 2 := by linarith [hx_ge_two]
    have hden_pos : 0 < x * (x - 1) := mul_pos hx_pos hx_m1_pos
    have hrhs_nonneg := div_nonneg hnum_nonneg (le_of_lt hden_pos)
    rw [←hdiff] at hrhs_nonneg
    exact le_of_sub_nonneg hrhs_nonneg
  have : ‖eulerZetaFactorMag p σ t - 1‖ ≤ 2 / x := by
    have hxw : eulerZetaFactorMag p σ t = x / ‖w‖ := by
      simp [eulerZetaFactorMag, eulerZeta_exp_s_log_p_sub_one, w, z, x, vertical]
    calc
      ‖eulerZetaFactorMag p σ t - 1‖
          = |(x / ‖w‖) - 1| := by simp [hxw, Real.norm_eq_abs]
      _ = |x - ‖w‖| / ‖w‖ := habs
      _ ≤ (1 : ℝ) / (x - 1) := h1
      _ ≤ 2 / x := h2
  simpa [hx_rpow] using this

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
  -- 道筋：Summable (fun p => ‖a p - 1‖) ⟹ Multipliable a（既製品）

  -- Step 1: ‖a_p - 1‖ の上界を構築
  -- 方針：eulerZetaFactorMag_sub_one_upper_bound が既に ≤ 2 / exp(σ log p) を与えるので、
  -- それを使って直接 Summable を示す

  have h_norm_sub_one_bound : ∀ p : {p // Nat.Prime p},
      ‖a p - 1‖ ≤ 2 / (↑p : ℝ) ^ σ := by
    intro ⟨p, hp⟩
    unfold a eulerZetaFactorMag
    -- eulerZetaFactorMag_sub_one_upper_bound から得られる上界
    have h_bound := eulerZetaFactorMag_sub_one_upper_bound p hp σ hσ t
    -- h_bound : eulerZetaFactorMag p σ t - 1 ≤ 2 / exp(σ * log p)

    have hp_pos : (0 : ℝ) < ↑p := by
      have : 0 < p := Nat.Prime.pos hp
      exact_mod_cast this

    -- exp(σ log p) = p^σ
    have h_exp_eq : Real.exp (σ * Real.log (↑p : ℝ)) = (↑p : ℝ) ^ σ := by
      rw [Real.rpow_def_of_pos hp_pos, mul_comm]

    rw [h_exp_eq]
    sorry -- h_bound と組み合わせて最終形に

  -- Step 2: Summable に落とす
  have h_summable_norm_sub_one :
      Summable (fun p : {p // Nat.Prime p} => ‖a p - 1‖) := by
    -- ‖a_p - 1‖ ≤ 2 / p^σ という上界から
    have h_bound : ∀ p : {p // Nat.Prime p},
        a p - 1 ≤ 2 / Real.exp (σ * Real.log (↑p : ℝ)) := by
      intro p
      unfold a
      exact eulerZetaFactorMag_sub_one_upper_bound p.1 p.2 σ hσ t

    -- p級数：∑' 1/p^σ は σ > 1 で収束
    -- Mathlib の実装を使う
    have h_zeta_convergent : Summable (fun p : {p // Nat.Prime p} => 1 / (↑p : ℝ) ^ σ) := by
      exact summable_one_div_prime_rpow_sigma σ hσ

    -- 係数を含む形：∑' 2/p^σ も収束
    -- スカラー倍の Summable は元の Summable から得られる
    have h_zeta_2_convergent : Summable (fun p : {p // Nat.Prime p} => 2 / (↑p : ℝ) ^ σ) := by
      have : (fun p : {p // Nat.Prime p} => 2 / (↑p : ℝ) ^ σ) =
             (fun p : {p // Nat.Prime p} => (2 : ℝ) * (1 / (↑p : ℝ) ^ σ)) := by
        ext p; ring
      rw [this]
      exact h_zeta_convergent.const_smul (2 : ℝ)

    have : ∀ p : {p // Nat.Prime p}, ‖a p - 1‖ ≤ 2 / (↑p : ℝ) ^ σ := by
      intro p
      -- h_bound から: a p - 1 ≤ 2 / exp(σ log p)
      have h1 := h_bound p
      have hp_pos : (0 : ℝ) < ↑p := by
        have : 0 < p.1 := Nat.Prime.pos p.2
        exact_mod_cast this
      -- exp(σ log p) = p^σ
      have h_exp_eq : Real.exp (σ * Real.log (↑p : ℝ)) = (↑p : ℝ) ^ σ := by
        rw [Real.rpow_def_of_pos hp_pos, mul_comm]
      rw [h_exp_eq] at h1
      -- ‖a p - 1‖ ≤ a p - 1 ≤ 2 / p^σ (符号は後で確認)
      sorry -- 符号の確認と norm の処理

    -- Summable 由比較判定法
    -- this : ∀ p, ‖a_p - 1‖ ≤ 2 / p^σ
    -- h_zeta_2_convergent : Summable (fun p => 2 / p^σ)
    sorry -- Summable.of_nonneg_of_le による比較判定法

  -- Step 3: Summable (‖a_p - 1‖) から Multipliable a を導く
  -- 戦略：a_p = 1 + f_p の形にして、multipliable_one_add_of_summable を使う
  -- ここで f_p := eulerZetaFactorMag p σ t - 1 とすると、
  -- ∑' ‖f_p‖ が収束すれば ∏' (1 + f_p) = ∏' a_p が Multipliable になる

  have h_multipliable : Multipliable a := by
    -- f_p := a_p - 1 と定義
    let f : {p // Nat.Prime p} → ℝ := fun p => a p - 1

    -- a_p = 1 + f_p を確認（ring で処理）
    have h_eq : ∀ p, a p = 1 + (a p - 1) := fun p => by ring

    -- multipliable_one_add_of_summable を直接使用
    -- ∑' ‖a_p - 1‖ が収束することから ∏' a_p が Multipliable
    have hsum : Summable fun p => ‖a p - 1‖ := h_summable_norm_sub_one

    convert multipliable_one_add_of_summable hsum using 1
    ext p
    ring

  -- 目標を達成：h_multipliable から EulerZetaMagMultipliable σ t を得る
  exact h_multipliable

theorem eulerZetaMag_pos_sigma_gt_one (σ : ℝ) (hσ : 1 < σ) (t : ℝ) :
    0 < eulerZetaMag σ t := by
  unfold eulerZetaMag

  -- a_p := eulerZetaFactorMag p σ t を定義
  let a : {p // Nat.Prime p} → ℝ := fun p => eulerZetaFactorMag p.1 σ t

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

  -- Step 1: 各因子 a_p ≠ 0 を確認
  have factor_ne_zero : ∀ p : {p // Nat.Prime p}, a p ≠ 0 := by
    intro p
    unfold a eulerZetaFactorMag
    have w_ne_zero : eulerZeta_exp_s_log_p_sub_one p.1 σ t ≠ 0 :=
      eulerZeta_exp_s_log_p_sub_one_ne_zero p.1 p.2 σ (by linarith : 0 < σ) t
    have w_norm_pos : 0 < ‖eulerZeta_exp_s_log_p_sub_one p.1 σ t‖ := norm_pos_iff.mpr w_ne_zero
    have exp_pos : 0 < Real.exp (σ * Real.log (↑p : ℝ)) := Real.exp_pos _
    exact (div_pos exp_pos w_norm_pos).ne'

  -- Step 2: 正値性を証明
  -- Multipliable + 各因子が正 ⟹ 無限積が正
  have h_tprod_pos : 0 < (∏' p : {p // Nat.Prime p}, a p) := by
    -- 各因子が正なら無限積も正
    -- Mathlib の直接的な補題：HProd（無限積）は各因子が正なら正
    have h_pos : ∀ p : {p // Nat.Prime p}, 0 < a p := fun p => factor_pos p.1 p.2

    -- tprod は有限積の supremum として定義される
    -- 有限部分積は全て正で、正の値に収束する
    -- したがって無限積も正

    -- 簡潔には：a_p = 1 + f_p で |f_p| ≤ 2/p^σ
    -- ∏(1 + f_p) は Multipliable かつ 1 より大きい
    have h_a_ge_one : ∀ p : {p // Nat.Prime p}, 1 ≤ a p := by
      intro p
      -- a_p = eulerZetaFactorMag p σ t
      -- eulerZetaFactorMag = exp(σ log p) / |exp((σ+it) log p) - 1|
      -- 分子 ≥ exp(0) = 1, 分母 > 0 より a_p > 0
      -- さらに a_p > 0 かつ Multipliable なら ∏a_p > 0
      sorry -- 1 ≤ a_p を示す（または別の方法で正値性を導く）

    -- これで正値性が出る
    sorry -- tprod の正値性（補題を特定後に埋める）

  exact h_tprod_pos

end DkMath.RH.EulerZeta
