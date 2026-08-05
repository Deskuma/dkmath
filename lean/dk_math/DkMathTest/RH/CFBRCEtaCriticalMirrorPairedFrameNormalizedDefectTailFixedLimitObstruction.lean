/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedDefectTailFixedLimitObstruction

set_option linter.style.longLine false

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameNormalizedDefectTailFixedLimitObstruction"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameNormalizedDefectTailFixedLimitObstruction

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

example (a : ℝ) (s : ℂ) (k : ℕ) :
    etaCriticalMirrorIndexNormalizedRotatedDefectTail a s k =
      etaPairBaseRotation s k *
        etaCriticalMirrorIndexNormalizedDefectTail a s k :=
  etaCriticalMirrorIndexNormalizedRotatedDefectTail_eq_baseRotation_mul a s k

example (z : ℂ) :
    etaPairIndexNormalizedTailConstant z ≠ 0 :=
  etaPairIndexNormalizedTailConstant_ne_zero z

example
    {s L : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    ¬ Tendsto
      (etaCriticalMirrorRightIndexNormalizedDefectTail s)
      atTop (nhds L) :=
  not_tendsto_etaCriticalMirrorRightIndexNormalizedDefectTail hs him hre

example
    {s L : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    ¬ Tendsto
      (etaCriticalMirrorLeftIndexNormalizedDefectTail s)
      atTop (nhds L) :=
  not_tendsto_etaCriticalMirrorLeftIndexNormalizedDefectTail hs him hre

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re ≠ (1 : ℝ) / 2) :
    EtaCriticalMirrorOffCriticalNormalizedDefectTailFixedLimitObstructionCertificate s :=
  etaCriticalMirrorOffCriticalNormalizedDefectTailFixedLimitObstructionCertificate_of_zero
    hs him hre

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameNormalizedDefectTailFixedLimitObstruction
