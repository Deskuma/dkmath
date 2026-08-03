/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorDefectKernelEventualSign

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorDefectKernelEventualSign"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorDefectKernelEventualSign

open Filter
open DkMath.RH.CFBRCProjection

example (s : ℂ) {x : ℝ} (hx : 0 < x) :
    0 < etaPairRadialDecay s x :=
  etaPairRadialDecay_pos s hx

example (s : ℂ) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    etaPairBaseRotation s k *
        etaCriticalMirrorDefectPairIntegralKernel s x =
      ((etaPairRadialDecay s x : ℝ) : ℂ) *
        (etaCriticalMirrorDefectCoefficient s x *
          etaPairResidualRotation s k x) :=
  etaPairBaseRotation_mul_defectPairIntegralKernel_factor s k hx

example {s : ℂ} (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    ∀ᶠ k : ℕ in atTop,
      ∀ x : ℝ,
        etaPairFrameLeftEndpoint k ≤ x →
        x ≤ etaPairFrameRightEndpoint k →
        0 < etaCriticalMirrorSignedVerticalProjection s
          (etaPairBaseRotation s k *
            etaCriticalMirrorDefectPairIntegralKernel s x) :=
  eventually_etaCriticalMirrorSignedVerticalProjection_baseRotation_mul_defectPairIntegralKernel_pos_on_pair
    him hre

example {s : ℂ} (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    ∀ᶠ k : ℕ in atTop,
      ∀ x : ℝ,
        etaPairFrameLeftEndpoint k ≤ x →
        x ≤ etaPairFrameRightEndpoint k →
        etaCriticalMirrorSignedVerticalProjection s
          (etaPairBaseRotation s k *
            etaCriticalMirrorDefectPairIntegralKernel s x) < 0 :=
  eventually_etaCriticalMirrorSignedVerticalProjection_baseRotation_mul_defectPairIntegralKernel_neg_on_pair
    him hre

end DkMathTest.RH.CFBRCEtaCriticalMirrorDefectKernelEventualSign
