/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.Defs
import DkMath.RH.EulerZeta

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
-- 1. Magnitude 定義の等価性（ここでは省略：定義段階で複数形を用意した）
-- ============================================================================

-- 注意：eulerZetaFactorMag, eulerZetaFactorMag_sqrt, eulerZetaFactorMag_normSq は
--       定義から見て等価だが、Lean が syntactically に認識するまでに
--       工夫が必要なため、将来的に必要になったら補題を追加する。

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

end DkMath.RH.EulerZeta
