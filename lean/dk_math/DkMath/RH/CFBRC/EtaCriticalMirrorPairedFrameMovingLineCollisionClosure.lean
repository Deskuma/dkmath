/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameMovingLineCollisionCore
import DkMath.RH.CFBRC.StandardZetaRealAxisClosure
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameMovingLineCollisionClosure"

noncomputable section

namespace DkMath.RH.CFBRCProjection

/--
The nonreal moving-line collision route, specialized to the concrete dominant
endpoint carrier, is unconditional once a genuine fixed global zero-line lock
is supplied.
-/
theorem etaCriticalMirror_nontrivialZero_re_eq_half_of_endpointGlobalZeroLineLock
    (hglobal :
      EtaCriticalMirrorGlobalZeroLineLock
        etaCriticalMirrorDominantNormalizedEndpointCarrier)
    {s : ℂ}
    (hs : NontrivialRiemannZetaZero s) :
    s.re = (1 : ℝ) / 2 := by
  exact etaCriticalMirror_re_eq_half_of_movingLine_globalLine_collision_core
    etaCriticalMirrorDominantNormalizedEndpointCarrier_localMovingLineLock
    etaCriticalMirrorDominantNormalizedEndpointCarrier_noncollapse
    hglobal hs (nontrivialRiemannZetaZero_im_ne_zero hs)

/--
The full Riemann Hypothesis follows from one remaining provider: a genuine
fixed global zero-line lock for the already constructed dominant endpoint
carrier.
-/
theorem riemannHypothesis_of_endpointGlobalZeroLineLock
    (hglobal :
      EtaCriticalMirrorGlobalZeroLineLock
        etaCriticalMirrorDominantNormalizedEndpointCarrier) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_nontrivialZero_re_eq_half]
  intro s hs
  exact
    etaCriticalMirror_nontrivialZero_re_eq_half_of_endpointGlobalZeroLineLock
      hglobal hs

#print axioms etaCriticalMirror_nontrivialZero_re_eq_half_of_endpointGlobalZeroLineLock
#print axioms riemannHypothesis_of_endpointGlobalZeroLineLock

end DkMath.RH.CFBRCProjection
