/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CFBRC.TrigBridge.Trig
import DkMath.CFBRC.TrigBridge.Complex

namespace DkMath.CFBRC.TrigBridge

theorem body2_eq_re_cfbrc2 (a φ : ℝ) :
    body2 (a * (1 - Real.sin φ)) (a * Real.sin φ) =
      Complex.re (cfbrcR 2 (a * Real.cos φ) (a * Real.sin φ)) := by
  rw [body2_trig, cfbrc_two_re_polar]

theorem factor_eq_re_cfbrc2 (a φ : ℝ) :
    (a * (1 - Real.sin φ)) * ((a * (1 - Real.sin φ)) + 2 * (a * Real.sin φ)) =
      Complex.re (cfbrcR 2 (a * Real.cos φ) (a * Real.sin φ)) := by
  rw [body2_factor_trig, cfbrc_two_re_polar]

end DkMath.CFBRC.TrigBridge
