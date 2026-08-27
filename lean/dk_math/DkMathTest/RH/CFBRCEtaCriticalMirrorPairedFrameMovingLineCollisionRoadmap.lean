/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameMovingLineCollisionClosure

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameMovingLineCollisionRoadmap

open DkMath.RH.CFBRCProjection

example {s : ℂ} (him : s.im ≠ 0) :
    EtaPairProjectiveTwoScaleNonresonanceCertificate s := by
  exact etaPairProjectiveTwoScaleNonresonanceCertificate_of_im_ne_zero him

example :
    EtaCriticalMirrorOffCriticalLocalMovingLineLock
      etaCriticalMirrorDominantNormalizedEndpointCarrier := by
  exact etaCriticalMirrorDominantNormalizedEndpointCarrier_localMovingLineLock

example :
    EtaCriticalMirrorOffCriticalCarrierNoncollapse
      etaCriticalMirrorDominantNormalizedEndpointCarrier := by
  exact etaCriticalMirrorDominantNormalizedEndpointCarrier_noncollapse

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

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameMovingLineCollisionRoadmap
