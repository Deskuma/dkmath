/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameMovingLineCollisionCore

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameMovingLineCollisionCore

open DkMath.RH.CFBRCProjection

example
    {carrier : ℕ → ℂ → ℂ}
    (hlocal : EtaCriticalMirrorOffCriticalLocalMovingLineLock carrier)
    (hnoncollapse : EtaCriticalMirrorOffCriticalCarrierNoncollapse carrier)
    (hglobal : EtaCriticalMirrorGlobalZeroLineLock carrier)
    {s : ℂ}
    (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    s.re = (1 : ℝ) / 2 := by
  exact etaCriticalMirror_re_eq_half_of_movingLine_globalLine_collision_core
    hlocal hnoncollapse hglobal hs him

example
    (hglobal :
      EtaCriticalMirrorGlobalZeroLineLock
        etaCriticalMirrorDominantNormalizedEndpointCarrier)
    {s : ℂ}
    (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    s.re = (1 : ℝ) / 2 := by
  exact etaCriticalMirror_re_eq_half_of_movingLine_globalLine_collision_core
    etaCriticalMirrorDominantNormalizedEndpointCarrier_localMovingLineLock
    etaCriticalMirrorDominantNormalizedEndpointCarrier_noncollapse
    hglobal hs him

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameMovingLineCollisionCore
