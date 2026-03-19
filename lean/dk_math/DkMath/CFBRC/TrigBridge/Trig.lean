/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CFBRC.TrigBridge.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace DkMath.CFBRC.TrigBridge

/-! # CFBRC TrigBridge: Trig Layer

三角置換 `x = a sin φ` により、代数 Body を

`a^2 - (a sin φ)^2 = a^2 cos^2 φ`

へ落とす層。
-/

/--
`sin^2 + cos^2 = 1` から導かれる二次恒等式。

`a^2 - (a sin φ)^2 = a^2 cos^2 φ`。
-/
lemma sq_sub_sin_eq_cos (a φ : ℝ) :
    a ^ 2 - (a * Real.sin φ) ^ 2 = a ^ 2 * (Real.cos φ) ^ 2 := by
  nlinarith [Real.sin_sq_add_cos_sq φ]

/--
三角置換後の Body 表示。

`body2 (a*(1-sin φ)) (a*sin φ) = a^2 cos^2 φ`。
-/
lemma body2_trig (a φ : ℝ) :
    body2 (a * (1 - Real.sin φ)) (a * Real.sin φ) = a ^ 2 * (Real.cos φ) ^ 2 := by
  calc
    body2 (a * (1 - Real.sin φ)) (a * Real.sin φ)
        = a ^ 2 - (a * Real.sin φ) ^ 2 := by
            simp [body2, pow_two]
            ring
    _ = a ^ 2 * (Real.cos φ) ^ 2 := sq_sub_sin_eq_cos a φ

/--
因数分解形から直接 `a^2 cos^2 φ` へ接続する補題。

`body2_factor` と `body2_trig` を連結したもの。
-/
lemma body2_factor_trig (a φ : ℝ) :
    (a * (1 - Real.sin φ)) * ((a * (1 - Real.sin φ)) + 2 * (a * Real.sin φ)) =
      a ^ 2 * (Real.cos φ) ^ 2 := by
  calc
    (a * (1 - Real.sin φ)) * ((a * (1 - Real.sin φ)) + 2 * (a * Real.sin φ))
        = body2 (a * (1 - Real.sin φ)) (a * Real.sin φ) := by
            symm
            exact body2_factor _ _
    _ = a ^ 2 * (Real.cos φ) ^ 2 := body2_trig a φ

end DkMath.CFBRC.TrigBridge
