/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedCoarseCorrectionObstruction

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameNormalizedCoarseCorrectionObstruction"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameNormalizedCoarseCorrectionObstruction

open DkMath.RH.CFBRCProjection

example
    (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    S.rightNormalizedBlockMarginConstant s < s.im ^ 2 / 8 :=
  S.rightNormalizedBlockMarginConstant_lt_im_sq_div_eight hs him

example
    (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    S.leftNormalizedBlockMarginConstant s < s.im ^ 2 / 8 :=
  S.leftNormalizedBlockMarginConstant_lt_im_sq_div_eight hs him

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    8 * s.im ^ 2 <
      etaCriticalMirrorRightLeftEndpointNormalizedCorrectionConstant s :=
  eight_mul_im_sq_lt_rightLeftEndpointNormalizedCorrectionConstant
    hs him hre

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    8 * s.im ^ 2 <
      etaCriticalMirrorLeftLeftEndpointNormalizedCorrectionConstant s :=
  eight_mul_im_sq_lt_leftLeftEndpointNormalizedCorrectionConstant
    hs him hre

example
    (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    S.rightNormalizedBlockMarginConstant s <
      etaCriticalMirrorRightLeftEndpointNormalizedCorrectionConstant s :=
  S.rightNormalizedBlockMarginConstant_lt_coarseCorrectionConstant
    hs him hre

example
    (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    S.leftNormalizedBlockMarginConstant s <
      etaCriticalMirrorLeftLeftEndpointNormalizedCorrectionConstant s :=
  S.leftNormalizedBlockMarginConstant_lt_coarseCorrectionConstant
    hs him hre

example
    (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    ¬ S.RightNormalizedAbelCorrectionConstantDominates s :=
  S.not_rightNormalizedAbelCorrectionConstantDominates hs him hre

example
    (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    ¬ S.LeftNormalizedAbelCorrectionConstantDominates s :=
  S.not_leftNormalizedAbelCorrectionConstantDominates hs him hre

example
    (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    S.rightNormalizedAbelCorrectionDominationGap s < 0 :=
  S.rightNormalizedAbelCorrectionDominationGap_neg hs him hre

example
    (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    S.leftNormalizedAbelCorrectionDominationGap s < 0 :=
  S.leftNormalizedAbelCorrectionDominationGap_neg hs him hre

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameNormalizedCoarseCorrectionObstruction
