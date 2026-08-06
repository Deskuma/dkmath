/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameBlockChord
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameBlockProjection"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

/--
Signed vertical projection of one defect pair viewed in the fixed frame at the
beginning of its finite block.
-/
noncomputable def etaCriticalMirrorBlockStartDefectPairProjection
    (s : ℂ) (K j : ℕ) : ℝ :=
  etaCriticalMirrorSignedVerticalProjection s
    (etaCriticalMirrorBlockStartRotatedDefectPairTerm s K j)

/--
The signed vertical projection is Lipschitz with constant `|s.im|` with
respect to the complex norm.
-/
theorem abs_etaCriticalMirrorSignedVerticalProjection_sub_le
    (s z w : ℂ) :
    |etaCriticalMirrorSignedVerticalProjection s z -
        etaCriticalMirrorSignedVerticalProjection s w| ≤
      |s.im| * ‖z - w‖ := by
  unfold etaCriticalMirrorSignedVerticalProjection
  have hdiff :
      s.im * z.im - s.im * w.im =
        s.im * (z - w).im := by
    simp
    ring
  rw [hdiff, abs_mul]
  exact
    mul_le_mul_of_nonneg_left
      (Complex.abs_im_le_norm (z - w))
      (abs_nonneg s.im)

/-- At the beginning of a block, the block frame and local frame agree. -/
theorem etaCriticalMirrorBlockStartDefectPairProjection_zero
    (s : ℂ) (K : ℕ) :
    etaCriticalMirrorBlockStartDefectPairProjection s K 0 =
      etaCriticalMirrorRotatedDefectPairProjection s K := by
  simp [etaCriticalMirrorBlockStartDefectPairProjection,
    etaCriticalMirrorBlockStartRotatedDefectPairTerm,
    etaCriticalMirrorRotatedDefectPairProjection,
    etaCriticalMirrorRotatedDefectPairTerm]

/--
The projection error caused by using the block-start frame instead of the
pair-local frame is bounded by the block angular span times the pair norm.
-/
theorem abs_etaCriticalMirrorBlockStartDefectPairProjection_sub_local_le
    (s : ℂ) (K j : ℕ)
    (hspan : etaPairFrameBlockSpan s K j ≤ 1) :
    |etaCriticalMirrorBlockStartDefectPairProjection s K j -
        etaCriticalMirrorRotatedDefectPairProjection s (K + j)| ≤
      2 * |s.im| * etaPairFrameBlockSpan s K j *
        ‖etaCriticalMirrorDefectPairTerm s (K + j)‖ := by
  calc
    |etaCriticalMirrorBlockStartDefectPairProjection s K j -
        etaCriticalMirrorRotatedDefectPairProjection s (K + j)| ≤
        |s.im| *
          ‖etaCriticalMirrorBlockStartRotatedDefectPairTerm s K j -
            etaCriticalMirrorRotatedDefectPairTerm s (K + j)‖ := by
      exact
        abs_etaCriticalMirrorSignedVerticalProjection_sub_le
          s
          (etaCriticalMirrorBlockStartRotatedDefectPairTerm s K j)
          (etaCriticalMirrorRotatedDefectPairTerm s (K + j))
    _ ≤
        |s.im| *
          (2 * etaPairFrameBlockSpan s K j *
            ‖etaCriticalMirrorDefectPairTerm s (K + j)‖) := by
      exact
        mul_le_mul_of_nonneg_left
          (norm_etaCriticalMirrorBlockStartRotatedDefectPairTerm_sub_local_le
            s K j hspan)
          (abs_nonneg s.im)
    _ =
        2 * |s.im| * etaPairFrameBlockSpan s K j *
          ‖etaCriticalMirrorDefectPairTerm s (K + j)‖ := by
      ring

/--
A positive local-frame projection remains positive in the block-start frame
whenever the frame-transfer error is smaller than the local positive margin.
-/
theorem etaCriticalMirrorBlockStartDefectPairProjection_pos_of_local_margin
    (s : ℂ) (K j : ℕ)
    (hspan : etaPairFrameBlockSpan s K j ≤ 1)
    (hmargin :
      2 * |s.im| * etaPairFrameBlockSpan s K j *
          ‖etaCriticalMirrorDefectPairTerm s (K + j)‖ <
        etaCriticalMirrorRotatedDefectPairProjection s (K + j)) :
    0 < etaCriticalMirrorBlockStartDefectPairProjection s K j := by
  have herror :
      |etaCriticalMirrorBlockStartDefectPairProjection s K j -
          etaCriticalMirrorRotatedDefectPairProjection s (K + j)| <
        etaCriticalMirrorRotatedDefectPairProjection s (K + j) :=
    lt_of_le_of_lt
      (abs_etaCriticalMirrorBlockStartDefectPairProjection_sub_local_le
        s K j hspan)
      hmargin
  have hlower := neg_lt_of_abs_lt herror
  linarith

/--
A negative local-frame projection remains negative in the block-start frame
whenever the frame-transfer error is smaller than the local negative margin.
-/
theorem etaCriticalMirrorBlockStartDefectPairProjection_neg_of_local_margin
    (s : ℂ) (K j : ℕ)
    (hspan : etaPairFrameBlockSpan s K j ≤ 1)
    (hmargin :
      2 * |s.im| * etaPairFrameBlockSpan s K j *
          ‖etaCriticalMirrorDefectPairTerm s (K + j)‖ <
        -etaCriticalMirrorRotatedDefectPairProjection s (K + j)) :
    etaCriticalMirrorBlockStartDefectPairProjection s K j < 0 := by
  have herror :
      |etaCriticalMirrorBlockStartDefectPairProjection s K j -
          etaCriticalMirrorRotatedDefectPairProjection s (K + j)| <
        -etaCriticalMirrorRotatedDefectPairProjection s (K + j) :=
    lt_of_le_of_lt
      (abs_etaCriticalMirrorBlockStartDefectPairProjection_sub_local_le
        s K j hspan)
      hmargin
  have hupper := lt_of_abs_lt herror
  linarith

end DkMath.RH.CFBRCProjection
