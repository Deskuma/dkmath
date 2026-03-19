/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CFBRC.TrigBridge.Trig
import DkMath.CFBRC.TrigBridge.Complex

namespace DkMath.CFBRC.TrigBridge

/-! # CFBRC TrigBridge: Main Theorems

代数層・三角層・複素層を束ね、`d=2` の橋

`(a' + x)^2 - x^2 = a'(a' + 2x) = a^2 cos^2 φ = Re G_2(a cos φ, a sin φ)`

を Lean 定理として固定する。
-/

/--
Body 形と CFBRC 実部の同一化（`d=2`）。

`body2 (a*(1-sin φ)) (a*sin φ) = Re(cfbrcR 2 (a cos φ) (a sin φ))`。
-/
theorem body2_eq_re_cfbrc2 (a φ : ℝ) :
    body2 (a * (1 - Real.sin φ)) (a * Real.sin φ) =
      Complex.re (cfbrcR 2 (a * Real.cos φ) (a * Real.sin φ)) := by
  rw [body2_trig, cfbrc_two_re_polar]

/--
因数分解形と CFBRC 実部の同一化（`d=2`）。

`(a*(1-sin φ))*((a*(1-sin φ)) + 2*(a*sin φ)) = Re(cfbrcR 2 (a cos φ) (a sin φ))`。
-/
theorem factor_eq_re_cfbrc2 (a φ : ℝ) :
    (a * (1 - Real.sin φ)) * ((a * (1 - Real.sin φ)) + 2 * (a * Real.sin φ)) =
      Complex.re (cfbrcR 2 (a * Real.cos φ) (a * Real.sin φ)) := by
  rw [body2_factor_trig, cfbrc_two_re_polar]

end DkMath.CFBRC.TrigBridge
