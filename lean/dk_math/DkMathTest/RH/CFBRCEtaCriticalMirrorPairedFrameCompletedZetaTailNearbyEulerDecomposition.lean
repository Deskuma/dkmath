/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaTailNearbyEulerDecomposition

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameCompletedZetaTailNearbyEulerDecomposition"

noncomputable section

namespace DkMathTest.RH.CFBRCProjection

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (k : ℕ) :
    etaCriticalMirrorDominantWeightedTailCarrier k s =
      etaCriticalMirrorDominantWeightedTailEulerMainCarrier k s +
        etaCriticalMirrorDominantWeightedTailEulerRemainderCarrier k s := by
  exact
    etaCriticalMirrorDominantWeightedTailCarrier_eq_eulerMain_add_remainder
      hs k

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (k : ℕ) :
    etaCriticalMirrorWeightedTailCompletedZetaNearbyTransverseBridgeError k s =
      etaCriticalMirrorWeightedTailCompletedZetaNearbyEulerMainTransverseError k s +
        etaCriticalMirrorWeightedTailEulerRemainderTransverseError k s := by
  exact
    etaCriticalMirrorWeightedTailCompletedZetaNearbyTransverseBridgeError_eq_eulerMain_add_remainder
      hs k

example
    (hmain :
      EtaCriticalMirrorWeightedTailCompletedZetaNearbyEulerMainTransverseCollapse)
    (hrem : EtaCriticalMirrorWeightedTailEulerRemainderTransverseCollapse) :
    EtaCriticalMirrorWeightedTailCompletedZetaNearbyTransverseBridgeCollapse := by
  exact
    etaCriticalMirrorWeightedTailCompletedZetaNearbyTransverseBridgeCollapse_of_eulerMain_and_remainder
      hmain hrem

example
    (hmain :
      EtaCriticalMirrorWeightedTailCompletedZetaNearbyEulerMainTransverseCollapse)
    (hrem : EtaCriticalMirrorWeightedTailEulerRemainderTransverseCollapse) :
    RiemannHypothesis := by
  exact
    riemannHypothesis_of_weightedTailCompletedZetaNearbyEulerMain_and_remainder
      hmain hrem

#print axioms completedRiemannZeta_eq_gammaR_mul_riemannZeta_of_pos_re
#print axioms etaCriticalMirrorDominantWeightedTailCarrier_eq_eulerMain_add_remainder
#print axioms etaCriticalMirrorWeightedTailCompletedZetaNearbyTransverseBridgeError_eq_eulerMain_add_remainder
#print axioms riemannHypothesis_of_weightedTailCompletedZetaNearbyEulerMain_and_remainder

end DkMathTest.RH.CFBRCProjection
