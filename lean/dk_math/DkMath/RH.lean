/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.Basic  -- Basic Definitions and Utilities
import DkMath.RH.Basic
import DkMath.RH.Defs
import DkMath.RH.Lemmas
import DkMath.RH.Theorems

-- ----------------------------------------------------------------------------

namespace DkMath.RH

open DkMath.Basic
open DkMath.RH.Basic

#eval printValue ident
#eval printValue name

end DkMath.RH

-- ----------------------------------------------------------------------------

namespace DkMath.RH

-- Lemmas for Riemann Hypothesis Module

open scoped Real
open Complex

/-
cid: 696f0dea-ce88-8322-9d20-8ce524dcd533

この定義は、次の「新しい見せ方」を Lean の定義として固定するためのもの。

$$
\frac{e^{\sigma\log p}}{\left|e^{(\sigma+it)\log p}-1\right|}
$$

(1) 素数 p ごとの因子（Euler-zeta factor）
    p^s / (p^s - 1)

(2) それを primes 全体で掛け合わせた無限積（tprod）
    ζ_e(s) := ∏_{p prime} p^s / (p^s - 1)

さらに、s = σ + i t の「位相シフト」表現や、
|exp((σ+it)log p) - 1| を使った “大きさ” の因子も別定義で置く。

注意:
- ここでは収束（Multipliable）や解析接続は証明しない。
- Lean の `∏'` は「収束するときにその極限、しないときは 1」という定義なので、
  “数学的に意味がある領域” は `Multipliable` 等の仮定とセットで使うのが作法。
-/

/-- Euler-zeta の素数因子:  p^s / (p^s - 1) -/
noncomputable def eulerZetaFactor (p : ℕ) (s : ℂ) : ℂ :=
  ((p : ℂ) ^ s) / (((p : ℂ) ^ s) - 1)

/-- ζ_e(s) を「素数全体の無限積」として定義（収束性は別途） -/
noncomputable def eulerZeta (s : ℂ) : ℂ :=
  ∏' p : {p // Nat.Prime p}, eulerZetaFactor p.1 s

/-- 縦線パラメータ s = σ + i t に代入した版 -/
noncomputable def eulerZeta_onVertical (σ t : ℝ) : ℂ :=
  eulerZeta (vertical σ t)

/-- vertical の実部は σ -/
lemma vertical_re (σ t : ℝ) : (vertical σ t).re = σ := by
  simp [vertical]

/-- vertical の虚部は t -/
lemma vertical_im (σ t : ℝ) : (vertical σ t).im = t := by
  simp [vertical]

/--
「標準化」: s = 1 を代入すると p/(p-1) になる（因子レベル）
-/
lemma eulerZetaFactor_one (p : ℕ) :
    eulerZetaFactor p (1 : ℂ) = (p : ℂ) / ((p : ℂ) - 1) := by
  simp [eulerZetaFactor]

/--
縦線版の標準化: σ=1, t=0 なら vertical 1 0 = 1 なので同じ形に落ちる
-/
lemma eulerZetaFactor_onVertical_std (p : ℕ) :
    eulerZetaFactor p (vertical 1 0) = (p : ℂ) / ((p : ℂ) - 1) := by
  -- vertical 1 0 = 1
  simp [vertical, eulerZetaFactor]

/-!
## “大きさ（magnitude）” の因子

$$
\frac{e^{\sigma\log p}}{\left|e^{(\sigma+it)\log p}-1\right|}
$$

ユーザー記述の

  exp(σ log p) / | exp((σ+it) log p) - 1 |

を、そのまま ℝ 値関数として定義する。

注意:
- これは複素値の因子そのものと等しいとは主張しない（等式化は別途の補題）。
- p は prime なので通常は p ≥ 2 で log p は素直に扱えるが、
  定義自体は総称的に書き、必要なら補題で条件を付ける。
-/

/-- ζ_e 分母: exp((σ+it) log p) - 1 という複素数 -/
noncomputable def eulerZeta_exp_s_log_p_sub_one (p : ℕ) (σ t : ℝ) : ℂ :=
    Complex.exp (vertical σ t * (Real.log (p : ℝ) : ℂ)) - 1

/-- magnitude 版の素数因子:
    exp(σ log p) / | exp((σ+it) log p) - 1 | -/
noncomputable def eulerZetaFactorMag (p : ℕ) (σ t : ℝ) : ℝ :=
  let w := eulerZeta_exp_s_log_p_sub_one p σ t
  Real.exp (σ * Real.log (p : ℝ)) / ‖w‖

noncomputable def eulerZetaFactorMag_sqrt (p : ℕ) (σ t : ℝ) : ℝ :=
  let w := eulerZeta_exp_s_log_p_sub_one p σ t
  Real.exp (σ * Real.log (p : ℝ)) /
    Real.sqrt (w.re * w.re + w.im * w.im)

noncomputable def eulerZetaFactorMag_normSq (p : ℕ) (σ t : ℝ) : ℝ :=
  let w := eulerZeta_exp_s_log_p_sub_one p σ t
  Real.exp (σ * Real.log (p : ℝ)) / Real.sqrt (Complex.normSq w)

lemma eulerZetaFactorMag_eq_sqrt (p : ℕ) (σ t : ℝ) :
    eulerZetaFactorMag p σ t = eulerZetaFactorMag_sqrt p σ t := by
    unfold eulerZetaFactorMag eulerZetaFactorMag_sqrt
    rfl

lemma eulerZetaFactorMag_eq_normSq (p : ℕ) (σ t : ℝ) :
    eulerZetaFactorMag p σ t = eulerZetaFactorMag_normSq p σ t := by
    unfold eulerZetaFactorMag eulerZetaFactorMag_normSq
    rfl

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

lemma eulerZetaFactorMag_sqrt_eq_normSq (p : ℕ) (σ t : ℝ) :
    eulerZetaFactorMag_sqrt p σ t = eulerZetaFactorMag_normSq p σ t := by
    unfold eulerZetaFactorMag_sqrt eulerZetaFactorMag_normSq
    simp only [Complex.normSq]
    rfl

/-- magnitude 版の “Euler-zeta” 無限積
    Euler-zeta: ∏'_{p prime} eulerZetaFactorMag p σ t -/
noncomputable def eulerZetaMag (σ t : ℝ) : ℝ :=
  ∏' p : {p // Nat.Prime p}, eulerZetaFactorMag p.1 σ t

/-- σ > 1 などの条件下で、素数全体の積が収束する、という主張の器 -/
def EulerZetaMagMultipliable (σ t : ℝ) : Prop :=
  Multipliable (fun p : {p // Nat.Prime p} => eulerZetaFactorMag p.1 σ t)

/-- 位相: arg( exp((σ+it)log p) - 1 ) -/
noncomputable def eulerZetaPhase (p : ℕ) (σ t : ℝ) : ℝ :=
  Complex.arg (eulerZeta_exp_s_log_p_sub_one p σ t)

end DkMath.RH
