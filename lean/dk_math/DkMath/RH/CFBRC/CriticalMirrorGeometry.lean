/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CompletedZetaBridge
import DkMath.RH.CFBRC.MirrorThreatModel

#print "file: DkMath.RH.CFBRC.CriticalMirrorGeometry"

namespace DkMath.RH.CFBRCProjection

/-- Reflection across the critical line while preserving the imaginary coordinate. -/
noncomputable def criticalMirror (s : ℂ) : ℂ :=
  ⟨1 - s.re, s.im⟩

@[simp] theorem criticalMirror_re (s : ℂ) :
    (criticalMirror s).re = 1 - s.re := by
  rfl

@[simp] theorem criticalMirror_im (s : ℂ) :
    (criticalMirror s).im = s.im := by
  rfl

end DkMath.RH.CFBRCProjection
