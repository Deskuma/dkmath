/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CFBRC.TrigBridge.Basic
import Mathlib.Tactic

namespace DkMath.CFBRC.TrigBridge

lemma cfbrc_two_re (X Θ : ℝ) :
    Complex.re (cfbrcR 2 X Θ) = X ^ 2 := by
  simp [cfbrcR, cfbrc, pow_two]

lemma cfbrc_two_im (X Θ : ℝ) :
    Complex.im (cfbrcR 2 X Θ) = 2 * X * Θ := by
  simp [cfbrcR, cfbrc, pow_two]
  ring

lemma cfbrc_two_re_polar (a φ : ℝ) :
    Complex.re (cfbrcR 2 (a * Real.cos φ) (a * Real.sin φ)) = a ^ 2 * (Real.cos φ) ^ 2 := by
  rw [cfbrc_two_re]
  ring

lemma cfbrc_two_im_polar (a φ : ℝ) :
    Complex.im (cfbrcR 2 (a * Real.cos φ) (a * Real.sin φ)) =
      2 * a ^ 2 * Real.sin φ * Real.cos φ := by
  rw [cfbrc_two_im]
  ring

end DkMath.CFBRC.TrigBridge
