/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorDefectPairQuantitativeMargin

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorDefectPairQuantitativeMargin"

set_option linter.style.longLine false

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorDefectPairQuantitativeMargin

open Filter
open DkMath.RH.CFBRCProjection

example (s : ℂ) (k : ℕ) : ℝ :=
  etaCriticalMirrorRightPairMargin s k

example (s : ℂ) (k : ℕ) : ℝ :=
  etaCriticalMirrorLeftPairMargin s k

example {s : ℂ} (him : s.im ≠ 0) (k : ℕ) :
    0 < etaCriticalMirrorRightPairMargin s k :=
  etaCriticalMirrorRightPairMargin_pos him k

example {s : ℂ} (him : s.im ≠ 0) (k : ℕ) :
    0 < etaCriticalMirrorLeftPairMargin s k :=
  etaCriticalMirrorLeftPairMargin_pos him k

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    ∀ᶠ k : ℕ in atTop,
      etaCriticalMirrorRightPairMargin s k ≤
        etaCriticalMirrorRotatedDefectPairProjection s k :=
  eventually_etaCriticalMirrorRightPairMargin_le_rotatedDefectPairProjection
    hs him hre

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    ∀ᶠ k : ℕ in atTop,
      etaCriticalMirrorLeftPairMargin s k ≤
        -etaCriticalMirrorRotatedDefectPairProjection s k :=
  eventually_etaCriticalMirrorLeftPairMargin_le_neg_rotatedDefectPairProjection
    hs him hre

end DkMathTest.RH.CFBRCEtaCriticalMirrorDefectPairQuantitativeMargin
