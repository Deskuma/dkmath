/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.OffCriticalExclusionGeneral

#print "file: DkMathTest.RH.CFBRCOffCriticalExclusionGeneral"

namespace DkMathTest.RH.CFBRCOffCriticalExclusionGeneral

open DkMath.RH.CFBRCProjection
open DkMath.CFBRC.TrigBridge

example (X Θ : ℝ) :
    cfbrcR 7 X Θ = 0 ↔ X = 0 := by
  exact cfbrcR_eq_zero_iff_x_eq_zero (by norm_num) X Θ

example (σ Θ : ℝ) :
    offCriticalCFBRC 11 σ Θ = 0 ↔ σ = (1 : ℝ) / 2 := by
  exact offCriticalCFBRC_eq_zero_iff_re_eq_half (by norm_num) σ Θ

variable (Zero : ℂ → Prop)

example
    (bridge : ZeroToCFBRCBridge Zero)
    {s : ℂ}
    (hs : Zero s) :
    s.re = (1 : ℝ) / 2 := by
  exact re_eq_half_of_zeroToCFBRCBridge bridge hs

end DkMathTest.RH.CFBRCOffCriticalExclusionGeneral
