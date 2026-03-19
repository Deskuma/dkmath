/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CFBRC.TrigBridge.Basic
import Mathlib.Tactic

namespace DkMath.CFBRC.TrigBridge

/-! # CFBRC TrigBridge: Complex Layer

`cfbrc 2 X Θ = (X + iΘ)^2 - (iΘ)^2` の実部・虚部を固定する層。
-/

/--
`d=2` の CFBRC 実部。

`Re ((X + iΘ)^2 - (iΘ)^2) = X^2`。
-/
lemma cfbrc_two_re (X Θ : ℝ) :
    Complex.re (cfbrcR 2 X Θ) = X ^ 2 := by
  simp [cfbrcR, cfbrc, pow_two]

/--
`d=2` の CFBRC 虚部。

`Im ((X + iΘ)^2 - (iΘ)^2) = 2XΘ`。
-/
lemma cfbrc_two_im (X Θ : ℝ) :
    Complex.im (cfbrcR 2 X Θ) = 2 * X * Θ := by
  simp [cfbrcR, cfbrc, pow_two]
  ring

/--
極座標代入 `X = a cos φ, Θ = a sin φ` 後の実部。

`Re (cfbrcR 2 (a cos φ) (a sin φ)) = a^2 cos^2 φ`。
-/
lemma cfbrc_two_re_polar (a φ : ℝ) :
    Complex.re (cfbrcR 2 (a * Real.cos φ) (a * Real.sin φ)) = a ^ 2 * (Real.cos φ) ^ 2 := by
  rw [cfbrc_two_re]
  ring

/--
極座標代入後の虚部。

`Im (cfbrcR 2 (a cos φ) (a sin φ)) = 2 a^2 sin φ cos φ`。
-/
lemma cfbrc_two_im_polar (a φ : ℝ) :
    Complex.im (cfbrcR 2 (a * Real.cos φ) (a * Real.sin φ)) =
      2 * a ^ 2 * Real.sin φ * Real.cos φ := by
  rw [cfbrc_two_im]
  ring

end DkMath.CFBRC.TrigBridge
