/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCosineLossBound

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameCosineLossBound"

noncomputable section

namespace DkMath.RH.CFBRCProjection

example (x : ℝ) :
    |Real.cos x - 1| ≤ x ^ 2 / 2 :=
  abs_cos_sub_one_le_sq_div_two x

example (s : ℂ) (k : ℕ) :
    |etaPairFrameStepPhase s k| ≤
      2 * (|s.im| / (((k + 1 : ℕ) : ℝ))) :=
  abs_etaPairFrameStepPhase_le_two_mul_abs_im_div_succ s k

example (s : ℂ) (k : ℕ) :
    ‖etaCriticalMirrorPairFrameTransportedDefectPartial s k‖ =
      ‖etaCriticalMirrorDefectPairedPartial (k + 1) s‖ :=
  norm_etaCriticalMirrorPairFrameTransportedDefectPartial s k

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (k : ℕ) :
    |etaCriticalMirrorPairedFrameCorrectionCosineLossTerm s k| ≤
      etaCriticalMirrorPairedFrameCosineLossMajorant s k :=
  abs_etaCriticalMirrorPairedFrameCorrectionCosineLossTerm_le_majorant
    hs him k

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    Summable (etaCriticalMirrorPairedFrameCorrectionCosineLossTerm s) :=
  summable_etaCriticalMirrorPairedFrameCorrectionCosineLossTerm hs him

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) {K : ℕ} (hK : 1 ≤ K) :
    |etaCriticalMirrorPairedFrameCorrectionCosineLossTail K s| ≤
      etaCriticalMirrorPairedFrameCorrectionCosineLossTailPowerBound s K :=
  abs_etaCriticalMirrorPairedFrameCorrectionCosineLossTail_le_powerBound
    hs him hK

end DkMath.RH.CFBRCProjection
