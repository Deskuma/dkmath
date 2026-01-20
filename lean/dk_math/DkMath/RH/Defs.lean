/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

-- ----------------------------------------------------------------------------

namespace DkMath.RH

-- Definitions for Riemann Hypothesis Module

/-- 縦線パス: s = σ + i t -/
def vertical (σ t : ℝ) : ℂ :=
  (σ : ℂ) + (t : ℂ) * Complex.I

/-- “トルク”(分子) : Re(z)*Im(dz) - Im(z)*Re(dz) -/
def torque (z dz : ℂ) : ℝ :=
  z.re * dz.im - z.im * dz.re

/-- 角速度の分母: Re(z)^2 + Im(z)^2 (= Complex.normSq z) -/
def denom (z : ℂ) : ℝ :=
  z.re^2 + z.im^2

/-- ドリフト消失（局所）: torque = 0 -/
def driftFreeLocal (z dz : ℂ) : Prop :=
  torque z dz = 0

/-- 位相速度: Im( (df/dt) / f ) -/
noncomputable def phaseVel (f : ℝ → ℂ) (t : ℝ) : ℝ :=
  ((deriv f t) / (f t)).im

/-- 位相のアンラップ: 初期位相 θ0 からの積分による位相の連続化 -/
noncomputable def phaseUnwrap (f : ℝ → ℂ) (t0 θ0 : ℝ) (t : ℝ) : ℝ :=
  θ0 + ∫ u in t0..t, phaseVel f u

/-- 点 t でのドリフト消失（関数版） -/
def driftFreeAt (f : ℝ → ℂ) (t : ℝ) : Prop :=
  driftFreeLocal (f t) (deriv f t)

end DkMath.RH

-- ----------------------------------------------------------------------------
