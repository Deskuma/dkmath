/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.RH.Basic  -- Riemann Hypothesis Basic Utilities
import DkMath.RH.Defs  -- Riemann Hypothesis Definitions

-- ----------------------------------------------------------------------------

namespace DkMath.RH

-- Lemmas for Riemann Hypothesis Module

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
lemma im_div_eq_torque_div_normSq {z dz : ℂ} :
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
        simpa using (im_div_eq_torque_div_normSq (z:=z) (dz:=dz))
      _ = 0 := by simp [driftFreeLocal] at h; simp [h]
  · intro h
    have h' : (torque z dz) / Complex.normSq z = 0 := by
      simpa [im_div_eq_torque_div_normSq (z:=z) (dz:=dz)] using h
    have h'' : torque z dz = 0 ∨ Complex.normSq z = 0 := (div_eq_zero_iff).1 h'
    have ht : torque z dz = 0 := h''.resolve_right hnorm
    simpa [driftFreeLocal] using ht

/-- トルクと共役複素数の積の虚部の等式 -/
lemma torque_eq_im_mul_conj (z dz : ℂ) :
    torque z dz = (dz * star z).im := by
  -- 展開して simp/ring
  simp only [torque, star, mul_im, mul_neg]
  ring

end DkMath.RH

-- ----------------------------------------------------------------------------

namespace DkMath.RH

open scoped Real
open Complex

/-- 位相速度とトルクの関係式 -/
lemma phaseVel_eq_torque_div_normSq (f : ℝ → ℂ) (t : ℝ) :
    phaseVel f t
      = (torque (f t) (deriv f t)) / (Complex.normSq (f t)) := by
  -- phaseVel の定義を開いて、すでにある代数コアへ接続
  simpa [phaseVel] using
    (im_div_eq_torque_div_normSq (z := f t) (dz := deriv f t))

end DkMath.RH

namespace DkMath.RH

open scoped Real
open Complex

/-- 局所ドリフト消失と位相速度ゼロの同値性 -/
lemma driftFreeLocal_iff_phaseVel_eq_zero
    (f : ℝ → ℂ) (t : ℝ) (hz : f t ≠ 0) :
    driftFreeLocal (f t) (deriv f t) ↔ phaseVel f t = 0 := by
  -- driftFreeLocal ↔ Im((deriv f t)/(f t))=0 ↔ phaseVel=0
  simpa [phaseVel] using
    (driftFreeLocal_iff_im_div_eq_zero (z := f t) (dz := deriv f t) hz)

end DkMath.RH
