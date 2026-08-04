/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameEtaTailEulerHalf

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameEtaTailEulerHalf"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.RH.Weave.Analytic

example {z : ℂ} (hz : z ≠ 0) (n : ℕ) :
    etaAdjacentDifference z n =
      ∫ x : ℝ in (((n + 1 : ℕ) : ℝ))..(((n + 2 : ℕ) : ℝ)),
        etaPairIntegralKernel z x :=
  etaAdjacentDifference_eq_intervalIntegral hz n

example {z : ℂ} (hzre : 0 < z.re) {x : ℝ} (hx : 0 < x) :
    ‖etaPairIntegralKernel z x - etaPairIntegralKernel z (x + 1)‖ ≤
      ‖z‖ * ‖z + 1‖ * x ^ (-z.re - 2) :=
  norm_etaPairIntegralKernel_sub_shift_le hzre hx

example {z : ℂ} (hzre : 0 < z.re) (j : ℕ) :
    ‖etaPairEulerSecondDifferenceTerm z j‖ ≤
      ‖z‖ * ‖z + 1‖ *
        (((2 * j + 1 : ℕ) : ℝ) ^ (-z.re - 2)) :=
  norm_etaPairEulerSecondDifferenceTerm_le hzre j

example {z : ℂ} (hzre : 0 < z.re) :
    Summable (etaPairEulerRemainderTerm z) :=
  summable_etaPairEulerRemainderTerm hzre

example {z : ℂ} (hzre : 0 < z.re)
    {K : ℕ} (hK : 1 ≤ K) :
    ‖etaPairEulerRemainderTail K z‖ ≤
      (‖z‖ * ‖z + 1‖ / 2) *
        (((K : ℝ) ^ (-z.re - 1)) / (z.re + 1)) :=
  norm_etaPairEulerRemainderTail_le hzre hK

example (z : ℂ) (j : ℕ) :
    etaPairTerm z j =
      etaPairEulerMainDifferenceTerm z j +
        etaPairEulerRemainderTerm z j :=
  etaPairTerm_eq_eulerMainDifference_add_remainder z j

example {z : ℂ} (hzre : 0 < z.re) (K : ℕ) :
    (∑' j : ℕ, etaPairEulerMainDifferenceTerm z (j + K)) =
      ((1 : ℂ) / 2) * etaUnsignedVector z (2 * K) :=
  tsum_etaPairEulerMainDifferenceTail hzre K

example {z : ℂ} (hzre : 0 < z.re) (K : ℕ) :
    etaPairTail K z =
      ((1 : ℂ) / 2) * etaUnsignedVector z (2 * K) +
        etaPairEulerRemainderTail K z :=
  etaPairTail_eq_half_endpoint_add_eulerRemainderTail hzre K

end DkMath.RH.CFBRCProjection
