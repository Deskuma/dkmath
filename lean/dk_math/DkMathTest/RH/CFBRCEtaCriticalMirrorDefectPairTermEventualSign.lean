/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorDefectPairTermEventualSign

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorDefectPairTermEventualSign"

set_option linter.style.longLine false

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorDefectPairTermEventualSign

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

example {s : ℂ} (hs : s ≠ 0) (hm : criticalMirror s ≠ 0)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    ∀ᶠ k : ℕ in atTop,
      0 < etaCriticalMirrorSignedVerticalProjection s
        (etaPairBaseRotation s k * etaCriticalMirrorDefectPairTerm s k) :=
  eventually_etaCriticalMirrorSignedVerticalProjection_baseRotation_mul_defectPairTerm_pos
    hs hm him hre

example {s : ℂ} (hs : s ≠ 0) (hm : criticalMirror s ≠ 0)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    ∀ᶠ k : ℕ in atTop,
      etaCriticalMirrorSignedVerticalProjection s
          (etaPairBaseRotation s k * etaCriticalMirrorDefectPairTerm s k) < 0 :=
  eventually_etaCriticalMirrorSignedVerticalProjection_baseRotation_mul_defectPairTerm_neg
    hs hm him hre

end DkMathTest.RH.CFBRCEtaCriticalMirrorDefectPairTermEventualSign
