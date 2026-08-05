/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CriticalMirrorZeroBridge
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameMovingLineCollisionRoadmap
import DkMath.RH.Weave.Analytic.EtaRealAxisPositivity
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.StandardZetaRealAxisClosure"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.RH.Weave.Analytic

/-- Every nontrivial Riemann-zeta zero is nonreal. -/
theorem nontrivialRiemannZetaZero_im_ne_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    s.im ≠ 0 := by
  intro him
  have hstrip := nontrivialRiemannZetaZero_mem_openCriticalStrip hs
  have hsreal : s = (s.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using him
  have hzreal : riemannZeta (s.re : ℂ) = 0 := by
    rw [← hsreal]
    exact hs.1
  exact
    (riemannZeta_ne_zero_of_real_mem_openCriticalInterval
      hstrip.1 hstrip.2) hzreal

/-- The real-axis closure provider is now unconditional. -/
theorem standardZetaRealAxisClosure :
    StandardZetaRealAxisClosure := by
  intro s hs him
  exact (nontrivialRiemannZetaZero_im_ne_zero hs him).elim

#print axioms nontrivialRiemannZetaZero_im_ne_zero
#print axioms standardZetaRealAxisClosure

end DkMath.RH.CFBRCProjection
