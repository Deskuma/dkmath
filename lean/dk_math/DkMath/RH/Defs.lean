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


end DkMath.RH

-- ----------------------------------------------------------------------------
