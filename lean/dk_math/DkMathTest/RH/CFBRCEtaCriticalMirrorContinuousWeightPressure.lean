/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorContinuousWeightPressure

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorContinuousWeightPressure"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorContinuousWeightPressure

open DkMath.RH.CFBRCProjection

example {s : ℂ} (hre : (1 : ℝ) / 2 < s.re)
    {x : ℝ} (hx : 1 < x) :
    1 < etaCriticalMirrorContinuousWeightR s x :=
  one_lt_etaCriticalMirrorContinuousWeightR_of_half_lt_re hre hx

example {s : ℂ} (hre : s.re < (1 : ℝ) / 2)
    {x : ℝ} (hx : 1 < x) :
    etaCriticalMirrorContinuousWeightR s x < 1 :=
  etaCriticalMirrorContinuousWeightR_lt_one_of_re_lt_half hre hx

example (s : ℂ) {x : ℝ} (hx : 1 < x) :
    etaCriticalMirrorContinuousWeightR s x = 1 ↔
      s.re = (1 : ℝ) / 2 :=
  etaCriticalMirrorContinuousWeightR_eq_one_iff_re_eq_half s hx

example {s : ℂ} (him : s.im ≠ 0)
    (hre : s.re ≠ (1 : ℝ) / 2)
    {x : ℝ} (hx : 1 < x) :
    etaCriticalMirrorDefectCoefficient s x ≠ 0 :=
  etaCriticalMirrorDefectCoefficient_ne_zero_of_im_ne_zero_of_re_ne_half
    him hre hx

end DkMathTest.RH.CFBRCEtaCriticalMirrorContinuousWeightPressure
