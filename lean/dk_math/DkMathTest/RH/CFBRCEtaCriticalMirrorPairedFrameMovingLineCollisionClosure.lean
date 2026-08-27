/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameMovingLineCollisionClosure

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameMovingLineCollisionClosure

open DkMath.RH.CFBRCProjection

example
    (hglobal :
      EtaCriticalMirrorGlobalZeroLineLock
        etaCriticalMirrorDominantNormalizedEndpointCarrier)
    {s : ℂ}
    (hs : NontrivialRiemannZetaZero s) :
    s.re = (1 : ℝ) / 2 := by
  exact
    etaCriticalMirror_nontrivialZero_re_eq_half_of_endpointGlobalZeroLineLock
      hglobal hs

example
    (hglobal :
      EtaCriticalMirrorGlobalZeroLineLock
        etaCriticalMirrorDominantNormalizedEndpointCarrier) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_endpointGlobalZeroLineLock hglobal

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameMovingLineCollisionClosure
