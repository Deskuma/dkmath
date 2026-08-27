/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.MirrorThreatModel

#print "file: DkMathTest.RH.CFBRCMirrorThreatModel"

namespace DkMathTest.RH.CFBRCMirrorThreatModel

open DkMath.RH.CFBRCProjection

example (d : ℕ) (X Θ : ℝ) :
    mirrorCFBRC d X Θ =
      (2 * (X : ℂ)) * mirrorCFBRCCore d X Θ := by
  exact mirrorCFBRC_eq_boundary_mul_core d X Θ

example (X Θ : ℝ) (hX : X ≠ 0) :
    mirrorCFBRC 7 X Θ = 0 ↔ mirrorCFBRCCore 7 X Θ = 0 := by
  exact mirrorCFBRC_eq_zero_iff_core_eq_zero hX

example (X Θ : ℝ) :
    mirrorCFBRC 3 X Θ = 0 ↔ X = 0 ∨ X ^ 2 = 3 * Θ ^ 2 := by
  exact mirrorCFBRC_three_eq_zero_iff X Θ

end DkMathTest.RH.CFBRCMirrorThreatModel
