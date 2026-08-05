/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameBlockProjection

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameBlockProjection"

set_option linter.style.longLine false

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameBlockProjection

open DkMath.RH.CFBRCProjection

example (s z w : ℂ) :
    |etaCriticalMirrorSignedVerticalProjection s z -
        etaCriticalMirrorSignedVerticalProjection s w| ≤
      |s.im| * ‖z - w‖ :=
  abs_etaCriticalMirrorSignedVerticalProjection_sub_le s z w

example (s : ℂ) (K : ℕ) :
    etaCriticalMirrorBlockStartDefectPairProjection s K 0 =
      etaCriticalMirrorRotatedDefectPairProjection s K :=
  etaCriticalMirrorBlockStartDefectPairProjection_zero s K

example
    (s : ℂ) (K j : ℕ)
    (hspan : etaPairFrameBlockSpan s K j ≤ 1) :
    |etaCriticalMirrorBlockStartDefectPairProjection s K j -
        etaCriticalMirrorRotatedDefectPairProjection s (K + j)| ≤
      2 * |s.im| * etaPairFrameBlockSpan s K j *
        ‖etaCriticalMirrorDefectPairTerm s (K + j)‖ :=
  abs_etaCriticalMirrorBlockStartDefectPairProjection_sub_local_le
    s K j hspan

example
    (s : ℂ) (K j : ℕ)
    (hspan : etaPairFrameBlockSpan s K j ≤ 1)
    (hmargin :
      2 * |s.im| * etaPairFrameBlockSpan s K j *
          ‖etaCriticalMirrorDefectPairTerm s (K + j)‖ <
        etaCriticalMirrorRotatedDefectPairProjection s (K + j)) :
    0 < etaCriticalMirrorBlockStartDefectPairProjection s K j :=
  etaCriticalMirrorBlockStartDefectPairProjection_pos_of_local_margin
    s K j hspan hmargin

example
    (s : ℂ) (K j : ℕ)
    (hspan : etaPairFrameBlockSpan s K j ≤ 1)
    (hmargin :
      2 * |s.im| * etaPairFrameBlockSpan s K j *
          ‖etaCriticalMirrorDefectPairTerm s (K + j)‖ <
        -etaCriticalMirrorRotatedDefectPairProjection s (K + j)) :
    etaCriticalMirrorBlockStartDefectPairProjection s K j < 0 :=
  etaCriticalMirrorBlockStartDefectPairProjection_neg_of_local_margin
    s K j hspan hmargin

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameBlockProjection
