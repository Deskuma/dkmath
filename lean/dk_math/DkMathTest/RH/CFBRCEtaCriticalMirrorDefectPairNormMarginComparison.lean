/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorDefectPairNormMarginComparison

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorDefectPairNormMarginComparison"

set_option linter.style.longLine false

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorDefectPairNormMarginComparison

open Filter
open DkMath.RH.CFBRCProjection

example (s : ℂ) :
    0 ≤ etaCriticalMirrorDefectPairNormCoefficient s :=
  etaCriticalMirrorDefectPairNormCoefficient_nonneg s

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (hre : (1 : ℝ) / 2 < s.re) :
    ∀ᶠ k : ℕ in atTop,
      (s.im ^ 2 / 4) * ‖etaCriticalMirrorDefectPairTerm s k‖ ≤
        etaCriticalMirrorDefectPairNormCoefficient s *
          etaCriticalMirrorRightPairMargin s k :=
  eventually_scaled_norm_etaCriticalMirrorDefectPairTerm_le_rightPairMargin
    hs hre

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (hre : s.re < (1 : ℝ) / 2) :
    ∀ᶠ k : ℕ in atTop,
      (s.im ^ 2 / 4) * ‖etaCriticalMirrorDefectPairTerm s k‖ ≤
        etaCriticalMirrorDefectPairNormCoefficient s *
          etaCriticalMirrorLeftPairMargin s k :=
  eventually_scaled_norm_etaCriticalMirrorDefectPairTerm_le_leftPairMargin
    hs hre

end DkMathTest.RH.CFBRCEtaCriticalMirrorDefectPairNormMarginComparison
