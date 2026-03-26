/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

--cid: 696f0dea-ce88-8322-9d20-8ce524dcd533

import Mathlib
import DkMath.Basic
import DkMath.RH.Basic
import DkMath.RH.Defs

#print "file: DkMath.RH.EulerZeta"

-- ============================================================================

namespace DkMath.RH.EulerZeta

open DkMath.Basic
open scoped Real
open scoped BigOperators
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
-- 4. 有限 Euler 積（HOPC-RH 観測量）
-- ============================================================================

/-- 有限素数集合で切った Euler-zeta 因子の複素積。 -/
noncomputable def eulerZetaFinite (S : Finset {p // Nat.Prime p}) (s : ℂ) : ℂ :=
  ∏ p ∈ S, eulerZetaFactor p.1 s

/-- 縦線上の有限 Euler 積。 -/
noncomputable def eulerZetaFinite_onVertical
    (S : Finset {p // Nat.Prime p}) (σ t : ℝ) : ℂ :=
  eulerZetaFinite S (vertical σ t)

/-- magnitude 因子の有限積（観測用）。 -/
noncomputable def eulerZetaMagFinite
    (S : Finset {p // Nat.Prime p}) (σ t : ℝ) : ℝ :=
  ∏ p ∈ S, eulerZetaFactorMag p.1 σ t

/-- `w_p(t) = exp((σ+it)log p)-1` の有限積（位相観測の母体）。 -/
noncomputable def eulerZetaExpSubOneFinite
    (S : Finset {p // Nat.Prime p}) (σ t : ℝ) : ℂ :=
  ∏ p ∈ S, eulerZeta_exp_s_log_p_sub_one p.1 σ t

/-- 縦線上 Euler 因子の exp 形（`exp / (exp-1)`）。 -/
noncomputable def eulerZetaFactorVerticalExp (p : ℕ) (σ t : ℝ) : ℂ :=
  Complex.exp (vertical σ t * (Real.log (p : ℝ) : ℂ)) /
    eulerZeta_exp_s_log_p_sub_one p σ t

/-- exp 形 Euler 因子の有限積。 -/
noncomputable def eulerZetaFactorVerticalExpFinite
    (S : Finset {p // Nat.Prime p}) (σ t : ℝ) : ℂ :=
  ∏ p ∈ S, eulerZetaFactorVerticalExp p.1 σ t

/--
素数 `p` に対する局所位相速度寄与。

`w_p(t) = exp((σ+it)log p) - 1` に `phaseVel` を適用した値。
-/
noncomputable def eulerZetaPhaseVelLocal (p : ℕ) (σ t : ℝ) : ℝ :=
  DkMath.RH.phaseVel (fun u : ℝ => eulerZeta_exp_s_log_p_sub_one p σ u) t

/-- 有限素数集合に対する局所位相速度寄与の和。 -/
noncomputable def eulerZetaPhaseVelFinite
    (S : Finset {p // Nat.Prime p}) (σ t : ℝ) : ℝ :=
  ∑ p ∈ S, eulerZetaPhaseVelLocal p.1 σ t

/-- exp 形 Euler 因子の局所位相速度寄与。 -/
noncomputable def eulerZetaFactorPhaseVelLocal (p : ℕ) (σ t : ℝ) : ℝ :=
  DkMath.RH.phaseVel (fun u : ℝ => eulerZetaFactorVerticalExp p σ u) t

/-- exp 形 Euler 因子の有限位相速度和。 -/
noncomputable def eulerZetaFactorPhaseVelFinite
    (S : Finset {p // Nat.Prime p}) (σ t : ℝ) : ℝ :=
  ∑ p ∈ S, eulerZetaFactorPhaseVelLocal p.1 σ t

/--
HOPC-RH における素数 `p` の局所位相寄与。

`log p - phaseVel(w_p)` を 1 つの観測量として束ねた名前。
-/
noncomputable def hopcPrimeLocalContribution (p : ℕ) (σ t : ℝ) : ℝ :=
  Real.log (p : ℝ) - eulerZetaPhaseVelLocal p σ t

/--
HOPC-RH の有限素数集合に対する局所位相寄与総和。
-/
noncomputable def hopcPrimeContributionSum
    (S : Finset {p // Nat.Prime p}) (σ t : ℝ) : ℝ :=
  ∑ p ∈ S, hopcPrimeLocalContribution p.1 σ t

-- ============================================================================
-- 5. 収束性の述語
-- ============================================================================

/-- magnitude 版の "Euler-zeta" が収束するという述語
    σ > 1 のときに成り立つことを証明するのが次のステップ
-/
def EulerZetaMagMultipliable (σ t : ℝ) : Prop :=
  Multipliable (fun p : {p // Nat.Prime p} => eulerZetaFactorMag p.1 σ t)

end DkMath.RH.EulerZeta
