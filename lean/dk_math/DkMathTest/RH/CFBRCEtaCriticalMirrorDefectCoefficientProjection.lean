/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorDefectCoefficientProjection

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorDefectCoefficientProjection"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorDefectCoefficientProjection

open DkMath.RH.CFBRCProjection

example (s : ℂ) {x : ℝ} (hx : 0 < x) :
    etaCriticalMirrorSignedVerticalProjection s
        (etaCriticalMirrorDefectCoefficient s x) =
      s.im ^ 2 *
        (etaCriticalMirrorContinuousWeightR s x - 1) :=
  etaCriticalMirrorSignedVerticalProjection_defectCoefficient_eq s hx

example {s : ℂ} (him : s.im ≠ 0)
    (hre : (1 : ℝ) / 2 < s.re)
    {x : ℝ} (hx : 1 < x) :
    0 <
      etaCriticalMirrorSignedVerticalProjection s
        (etaCriticalMirrorDefectCoefficient s x) :=
  etaCriticalMirrorSignedVerticalProjection_defectCoefficient_pos_of_half_lt_re
    him hre hx

example {s : ℂ} (him : s.im ≠ 0)
    (hre : s.re < (1 : ℝ) / 2)
    {x : ℝ} (hx : 1 < x) :
    etaCriticalMirrorSignedVerticalProjection s
        (etaCriticalMirrorDefectCoefficient s x) < 0 :=
  etaCriticalMirrorSignedVerticalProjection_defectCoefficient_neg_of_re_lt_half
    him hre hx

example (s : ℂ) (him : s.im ≠ 0)
    {x : ℝ} (hx : 1 < x) :
    (s.re < (1 : ℝ) / 2 ∧
      etaCriticalMirrorSignedVerticalProjection s
          (etaCriticalMirrorDefectCoefficient s x) < 0) ∨
    (s.re = (1 : ℝ) / 2 ∧
      etaCriticalMirrorSignedVerticalProjection s
          (etaCriticalMirrorDefectCoefficient s x) = 0) ∨
    ((1 : ℝ) / 2 < s.re ∧
      0 < etaCriticalMirrorSignedVerticalProjection s
          (etaCriticalMirrorDefectCoefficient s x)) :=
  etaCriticalMirrorSignedVerticalProjection_defectCoefficient_sign_trichotomy
    s him hx

end DkMathTest.RH.CFBRCEtaCriticalMirrorDefectCoefficientProjection
