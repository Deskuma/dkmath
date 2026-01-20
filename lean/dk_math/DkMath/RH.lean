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

/-- 分母の定義と基本補題群 -/
lemma denom_eq_normSq (z : ℂ) : denom z = Complex.normSq z := by
  simp [denom, Complex.normSq]
  ring

/--
代数コア:
z ≠ 0 のとき、Im(dz / z) = torque z dz / normSq z
（文書の dθ/dt 公式の“形”そのもの）
-/
lemma im_div_eq_torque_div_normSq {z dz : ℂ} (_hz : z ≠ 0) :
    (dz / z).im = (torque z dz) / (Complex.normSq z) := by
  -- dz / z = dz * (conj z) / normSq z を使って展開するのが定石
  -- ここは `simp` + `ring` で落ちることが多い
  calc
    (dz / z).im = dz.im * z.re / Complex.normSq z - dz.re * z.im / Complex.normSq z := by
      simp only [div_im]
    _ = (dz.im * z.re - dz.re * z.im) / Complex.normSq z := by
      simpa using (sub_div (dz.im * z.re) (dz.re * z.im) (Complex.normSq z)).symm
    _ = (z.re * dz.im - z.im * dz.re) / Complex.normSq z := by
      ring
    _ = (torque z dz) / Complex.normSq z := by
      simp [torque]

/-- ドリフト消失（局所）: torque = 0 -/
def driftFreeLocal (z dz : ℂ) : Prop :=
  torque z dz = 0

/--
局所ドリフト消失は Im(dz/z)=0 と同値（z≠0）。
-/
lemma driftFreeLocal_iff_im_div_eq_zero {z dz : ℂ} (hz : z ≠ 0) :
    driftFreeLocal z dz ↔ (dz / z).im = 0 := by
  -- 上の代数コアを使って分母を払う
  have hnorm : Complex.normSq z ≠ 0 := by
    intro h0
    exact hz ((Complex.normSq_eq_zero).1 h0)
  constructor
  · intro h
    calc
      (dz / z).im = (torque z dz) / Complex.normSq z := by
        simpa using (im_div_eq_torque_div_normSq (z:=z) (dz:=dz) hz)
      _ = 0 := by simp [driftFreeLocal] at h; simp [h]
  · intro h
    have h' : (torque z dz) / Complex.normSq z = 0 := by
      simpa [im_div_eq_torque_div_normSq (z:=z) (dz:=dz) hz] using h
    have h'' : torque z dz = 0 ∨ Complex.normSq z = 0 := (div_eq_zero_iff).1 h'
    have ht : torque z dz = 0 := h''.resolve_right hnorm
    simpa [driftFreeLocal] using ht


end DkMath.RH
