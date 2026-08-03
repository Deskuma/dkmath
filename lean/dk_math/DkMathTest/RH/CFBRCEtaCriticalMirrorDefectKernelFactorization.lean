/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorDefectKernelFactorization

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorDefectKernelFactorization"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorDefectKernelFactorization

open DkMath.RH.CFBRCProjection

example (s : ℂ) {x : ℝ} (hx : 0 < x) :
    etaCriticalMirrorDefectPairIntegralKernel s x =
      etaCriticalMirrorDefectCoefficient s x *
        (x : ℂ) ^ (-s - 1) :=
  etaCriticalMirrorDefectPairIntegralKernel_factor s hx

example (s : ℂ) {x : ℝ} (hx : 0 < x) :
    (etaCriticalMirrorDefectCoefficient s x).re =
      (1 - s.re) * etaCriticalMirrorContinuousWeightR s x - s.re :=
  etaCriticalMirrorDefectCoefficient_re s hx

example (s : ℂ) {x : ℝ} (hx : 0 < x) :
    (etaCriticalMirrorDefectCoefficient s x).im =
      s.im * (etaCriticalMirrorContinuousWeightR s x - 1) :=
  etaCriticalMirrorDefectCoefficient_im s hx

example {s : ℂ} (hre : s.re = (1 : ℝ) / 2)
    {x : ℝ} (hx : 0 < x) :
    etaCriticalMirrorDefectPairIntegralKernel s x = 0 :=
  etaCriticalMirrorDefectPairIntegralKernel_eq_zero_of_re_eq_half hre hx

end DkMathTest.RH.CFBRCEtaCriticalMirrorDefectKernelFactorization
