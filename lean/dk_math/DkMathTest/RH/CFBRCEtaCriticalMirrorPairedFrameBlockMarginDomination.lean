/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameBlockMarginDomination

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameBlockMarginDomination"

set_option linter.style.longLine false

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameBlockMarginDomination

open Filter
open DkMath.RH.CFBRCProjection

example (s : ℂ) (j : ℕ) :
    ∀ᶠ K : ℕ in atTop,
      etaPairFrameBlockSpan s K j ≤ 1 :=
  eventually_etaPairFrameBlockSpan_le_one s j

example {s : ℂ} (him : s.im ≠ 0) (j : ℕ) :
    ∀ᶠ K : ℕ in atTop,
      8 * etaCriticalMirrorDefectPairNormCoefficient s *
          etaPairFrameBlockSpan s K j <
        |s.im| :=
  eventually_eight_mul_normCoefficient_mul_blockSpan_lt_abs_im him j

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re)
    (j : ℕ) :
    ∀ᶠ K : ℕ in atTop,
      2 * |s.im| * etaPairFrameBlockSpan s K j *
          ‖etaCriticalMirrorDefectPairTerm s (K + j)‖ <
        etaCriticalMirrorRightPairMargin s (K + j) :=
  eventually_etaCriticalMirrorBlockTransferError_lt_rightPairMargin
    hs him hre j

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2)
    (j : ℕ) :
    ∀ᶠ K : ℕ in atTop,
      2 * |s.im| * etaPairFrameBlockSpan s K j *
          ‖etaCriticalMirrorDefectPairTerm s (K + j)‖ <
        etaCriticalMirrorLeftPairMargin s (K + j) :=
  eventually_etaCriticalMirrorBlockTransferError_lt_leftPairMargin
    hs him hre j

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re)
    (j : ℕ) :
    ∀ᶠ K : ℕ in atTop,
      0 < etaCriticalMirrorBlockStartDefectPairProjection s K j :=
  eventually_etaCriticalMirrorBlockStartDefectPairProjection_pos_of_half_lt_re
    hs him hre j

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2)
    (j : ℕ) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorBlockStartDefectPairProjection s K j < 0 :=
  eventually_etaCriticalMirrorBlockStartDefectPairProjection_neg_of_re_lt_half
    hs him hre j

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameBlockMarginDomination
