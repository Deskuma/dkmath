/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaTailNearbyEulerRemainderCollapse

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameCompletedZetaTailNearbyEulerRemainderCollapse"

noncomputable section

namespace DkMathTest.RH.CFBRCProjection

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

example
    {a : ℝ} {z : ℂ} (hzre : 0 < z.re) (ha : a ≤ z.re) :
    Tendsto
      (etaPairIndexScaledEulerRemainder a z)
      atTop (nhds 0) := by
  exact etaPairIndexScaledEulerRemainder_tendsto_zero hzre ha

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    Tendsto
      (fun k : ℕ =>
        etaCriticalMirrorDominantWeightedTailEulerRemainderCarrier k s)
      atTop (nhds 0) := by
  exact
    etaCriticalMirrorDominantWeightedTailEulerRemainderCarrier_tendsto_zero hs

example :
    EtaCriticalMirrorWeightedTailEulerRemainderTransverseCollapse := by
  exact etaCriticalMirrorWeightedTailEulerRemainderTransverseCollapse

example :
    EtaCriticalMirrorWeightedTailCompletedZetaNearbyTransverseBridgeCollapse ↔
      EtaCriticalMirrorWeightedTailCompletedZetaNearbyEulerMainTransverseCollapse := by
  exact
    etaCriticalMirrorWeightedTailCompletedZetaNearbyTransverseBridgeCollapse_iff_eulerMain

example
    (hmain :
      EtaCriticalMirrorWeightedTailCompletedZetaNearbyEulerMainTransverseCollapse) :
    RiemannHypothesis := by
  exact
    riemannHypothesis_of_weightedTailCompletedZetaNearbyEulerMainTransverseCollapse
      hmain

#print axioms etaPairIndexScaledEulerRemainder_tendsto_zero
#print axioms etaCriticalMirrorDominantWeightedTailEulerRemainderCarrier_tendsto_zero
#print axioms etaCriticalMirrorWeightedTailEulerRemainderTransverseCollapse
#print axioms etaCriticalMirrorWeightedTailCompletedZetaNearbyTransverseBridgeCollapse_iff_eulerMain
#print axioms riemannHypothesis_of_weightedTailCompletedZetaNearbyEulerMainTransverseCollapse

end DkMathTest.RH.CFBRCProjection
