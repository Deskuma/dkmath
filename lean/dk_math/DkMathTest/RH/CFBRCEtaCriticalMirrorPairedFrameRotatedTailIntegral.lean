/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameRotatedTailIntegral

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameRotatedTailIntegral"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.RH.Weave.Analytic

example (s : ℂ) (k : ℕ) :
    etaPairBaseRotation (criticalMirror s) k =
      etaPairBaseRotation s k :=
  etaPairBaseRotation_criticalMirror s k

example (s : ℂ) (k : ℕ) (x : ℝ) :
    etaPairResidualRotation (criticalMirror s) k x =
      etaPairResidualRotation s k x :=
  etaPairResidualRotation_criticalMirror s k x

example (s : ℂ) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    etaPairBaseRotation s k * etaPairIntegralKernel s x =
      ((etaPairRadialDecay s x : ℝ) : ℂ) *
        (s * etaPairResidualRotation s k x) :=
  etaPairBaseRotation_mul_originalEtaPairIntegralKernel_factor s k hx

example (s : ℂ) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    etaPairBaseRotation s k *
        etaPairIntegralKernel (criticalMirror s) x =
      ((etaPairRadialDecay (criticalMirror s) x : ℝ) : ℂ) *
        (criticalMirror s * etaPairResidualRotation s k x) :=
  etaPairBaseRotation_mul_mirrorEtaPairIntegralKernel_factor s k hx

example {z : ℂ} (hz : z ≠ 0) (s : ℂ) (k j : ℕ) :
    etaPairBaseRotation s k * etaPairTerm z j =
      ∫ x : ℝ in
          (etaPairFrameLeftEndpoint j)..(etaPairFrameRightEndpoint j),
        etaPairBaseRotation s k * etaPairIntegralKernel z x :=
  etaPairBaseRotation_mul_singleEtaPairTerm_eq_intervalIntegral hz s k j

example {s : ℂ} (hs : NontrivialRiemannZetaZero s) (k : ℕ) :
    Summable
      (etaCriticalMirrorPairFrameRotatedOriginalTailIntegralTerm s k) :=
  summable_etaCriticalMirrorPairFrameRotatedOriginalTailIntegralTerm hs k

example {s : ℂ} (hs : NontrivialRiemannZetaZero s) (k : ℕ) :
    etaCriticalMirrorPairFrameRotatedOriginalTail s k =
      ∑' j : ℕ,
        etaCriticalMirrorPairFrameRotatedOriginalTailIntegralTerm s k j :=
  etaCriticalMirrorPairFrameRotatedOriginalTail_eq_tsum_intervalIntegral hs k

example {s : ℂ} (hs : NontrivialRiemannZetaZero s) (k : ℕ) :
    etaCriticalMirrorPairFrameRotatedMirrorTail s k =
      ∑' j : ℕ,
        etaCriticalMirrorPairFrameRotatedMirrorTailIntegralTerm s k j :=
  etaCriticalMirrorPairFrameRotatedMirrorTail_eq_tsum_intervalIntegral hs k

example {s : ℂ} (hs : NontrivialRiemannZetaZero s) (k : ℕ) :
    (etaCriticalMirrorPairFrameRotatedOriginalTail s k).re =
      ∑' j : ℕ,
        (etaCriticalMirrorPairFrameRotatedOriginalTailIntegralTerm s k j).re :=
  etaCriticalMirrorPairFrameRotatedOriginalTail_re_eq_tsum_intervalIntegral_re hs k

end DkMath.RH.CFBRCProjection
