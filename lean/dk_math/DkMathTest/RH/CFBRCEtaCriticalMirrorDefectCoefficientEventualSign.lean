/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorDefectCoefficientEventualSign

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorDefectCoefficientEventualSign"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorDefectCoefficientEventualSign

open Filter
open DkMath.RH.CFBRCProjection

example {s : ℂ} (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    ∀ᶠ k : ℕ in atTop,
      ∀ x : ℝ,
        etaPairFrameLeftEndpoint k ≤ x →
        x ≤ etaPairFrameRightEndpoint k →
        0 < etaCriticalMirrorSignedVerticalProjection s
          (etaCriticalMirrorDefectCoefficient s x *
            etaPairResidualRotation s k x) :=
  eventually_etaCriticalMirrorSignedVerticalProjection_defectCoefficient_mul_residual_pos_on_pair
    him hre

example {s : ℂ} (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    ∀ᶠ k : ℕ in atTop,
      ∀ x : ℝ,
        etaPairFrameLeftEndpoint k ≤ x →
        x ≤ etaPairFrameRightEndpoint k →
        etaCriticalMirrorSignedVerticalProjection s
          (etaCriticalMirrorDefectCoefficient s x *
            etaPairResidualRotation s k x) < 0 :=
  eventually_etaCriticalMirrorSignedVerticalProjection_defectCoefficient_mul_residual_neg_on_pair
    him hre

end DkMathTest.RH.CFBRCEtaCriticalMirrorDefectCoefficientEventualSign
