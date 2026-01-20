/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.Basic
import DkMath.RH.Basic
import DkMath.RH.Defs

-- ============================================================================

namespace DkMath.RH.EulerZeta

open DkMath.Basic
open scoped Real
open Complex

/-
定義のみのモジュール：Euler-zeta の表現を形式化する

主な役割：
1. 複素版（解析的な定義）
2. "大きさ"（magnitude）版（実数値、収束評価用）
3. 位相関数
-/

-- ============================================================================
-- 1. 複素版の Euler-zeta 因子と無限積
-- ============================================================================

/-- Euler-zeta の素数因子:  p^s / (p^s - 1) -/
noncomputable def eulerZetaFactor (p : ℕ) (s : ℂ) : ℂ :=
  ((p : ℂ) ^ s) / (((p : ℂ) ^ s) - 1)

/-- ζ_e(s) を「素数全体の無限積」として定義（収束性は別途） -/
noncomputable def eulerZeta (s : ℂ) : ℂ :=
  ∏' p : {p // Nat.Prime p}, eulerZetaFactor p.1 s

/-- 縦線パラメータ s = σ + i t に代入した版 -/
noncomputable def eulerZeta_onVertical (σ t : ℝ) : ℂ :=
  eulerZeta (vertical σ t)

-- ============================================================================
-- 2. Magnitude版の Euler-zeta（実数値、収束評価用）
-- ============================================================================

/-- ζ_e 分母: exp((σ+it) log p) - 1 という複素数
    これが "分子・分母の位相シフト表現" の核となる
-/
noncomputable def eulerZeta_exp_s_log_p_sub_one (p : ℕ) (σ t : ℝ) : ℂ :=
    Complex.exp (vertical σ t * (Real.log (p : ℝ) : ℂ)) - 1

/-- magnitude 版の素数因子:
    exp(σ log p) / | exp((σ+it) log p) - 1 |

    ここで ‖w‖ は w の norm (= 複素数の absolute value)
-/
noncomputable def eulerZetaFactorMag (p : ℕ) (σ t : ℝ) : ℝ :=
  let w := eulerZeta_exp_s_log_p_sub_one p σ t
  Real.exp (σ * Real.log (p : ℝ)) / ‖w‖

/-- magnitude 版の「平方根表記」バージョン
    ‖w‖ = √(w.re² + w.im²) として書き下したもの
-/
noncomputable def eulerZetaFactorMag_sqrt (p : ℕ) (σ t : ℝ) : ℝ :=
  let w := eulerZeta_exp_s_log_p_sub_one p σ t
  Real.exp (σ * Real.log (p : ℝ)) /
    Real.sqrt (w.re * w.re + w.im * w.im)

/-- magnitude 版の「normSq 表記」バージョン
    Complex.normSq w = w.re² + w.im² を使う形
-/
noncomputable def eulerZetaFactorMag_normSq (p : ℕ) (σ t : ℝ) : ℝ :=
  let w := eulerZeta_exp_s_log_p_sub_one p σ t
  Real.exp (σ * Real.log (p : ℝ)) / Real.sqrt (Complex.normSq w)

/-- magnitude 版の "Euler-zeta" 無限積
    ∏'_{p prime} eulerZetaFactorMag p σ t
-/
noncomputable def eulerZetaMag (σ t : ℝ) : ℝ :=
  ∏' p : {p // Nat.Prime p}, eulerZetaFactorMag p.1 σ t

-- ============================================================================
-- 3. 位相関数（phase）
-- ============================================================================

/-- 位相: arg( exp((σ+it)log p) - 1 ) -/
noncomputable def eulerZetaPhase (p : ℕ) (σ t : ℝ) : ℝ :=
  Complex.arg (eulerZeta_exp_s_log_p_sub_one p σ t)

-- ============================================================================
-- 3.5 Magnitude 定義の等価性補題
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
-- 4. 収束性の述語
-- ============================================================================

/-- magnitude 版の "Euler-zeta" が収束するという述語
    σ > 1 のときに成り立つことを証明するのが次のステップ
-/
def EulerZetaMagMultipliable (σ t : ℝ) : Prop :=
  Multipliable (fun p : {p // Nat.Prime p} => eulerZetaFactorMag p.1 σ t)

end DkMath.RH.EulerZeta
