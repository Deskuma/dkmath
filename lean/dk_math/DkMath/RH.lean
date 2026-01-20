/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.Basic  -- Basic Definitions and Utilities
import DkMath.RH.Basic

-- ----------------------------------------------------------------------------

namespace DkMath.RH

open DkMath.Basic
open DkMath.RH.Basic

#eval printValue ident
#eval printValue name

end DkMath.RH

-- ----------------------------------------------------------------------------

namespace DkMath.RH

open scoped Real
open Complex

/-- 縦線パス: s = σ + i t -/
def vertical (σ t : ℝ) : ℂ :=
  (σ : ℂ) + (t : ℂ) * Complex.I

/-- “トルク”(分子) : Re(z)*Im(dz) - Im(z)*Re(dz) -/
def torque (z dz : ℂ) : ℝ :=
  z.re * dz.im - z.im * dz.re

/-- 角速度の分母: Re(z)^2 + Im(z)^2 (= Complex.normSq z) -/
def denom (z : ℂ) : ℝ :=
  z.re^2 + z.im^2

lemma denom_eq_normSq (z : ℂ) : denom z = Complex.normSq z := by
  simp [denom, Complex.normSq]
  ring

/--
代数コア:
z ≠ 0 のとき、Im(dz / z) = torque z dz / normSq z
（文書の dθ/dt 公式の“形”そのもの）
-/
lemma im_div_eq_torque_div_normSq {z dz : ℂ} (hz : z ≠ 0) :
    (dz / z).im = (torque z dz) / (Complex.normSq z) := by
  -- dz / z = dz * (conj z) / normSq z を使って展開するのが定石
  -- ここは `simp` + `ring` で落ちることが多い
  -- TODO: 仕上げ（必要なら段階的に補題を切る）
  admit

/-- ドリフト消失（局所）: torque = 0 -/
def driftFreeLocal (z dz : ℂ) : Prop :=
  torque z dz = 0

/--
局所ドリフト消失は Im(dz/z)=0 と同値（z≠0）。
-/
lemma driftFreeLocal_iff_im_div_eq_zero {z dz : ℂ} (hz : z ≠ 0) :
    driftFreeLocal z dz ↔ (dz / z).im = 0 := by
  -- 上の代数コアを使って分母を払う
  -- TODO: normSq z ≠ 0 を `Complex.normSq_ne_zero` などで出す
  admit


end DkMath.RH
