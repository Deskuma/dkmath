/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameFiniteBlockCertificate
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameGrowingBlockGeometry"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/--
A growing block schedule whose length tends to infinity while remaining
asymptotically negligible compared with the left endpoint `2K+1`.
-/
structure EtaPairGrowingBlockSchedule where
  blockLength : ℕ → ℕ
  blockLength_tendsto_atTop : Tendsto blockLength atTop atTop
  relativeLength_tendsto_zero :
    Tendsto
      (fun K : ℕ =>
        (blockLength K : ℝ) / etaPairFrameLeftEndpoint K)
      atTop (nhds 0)

/--
The angular span of a finite block is bounded by twice its relative length,
multiplied by `|s.im|`.
-/
theorem etaPairFrameBlockSpan_le_two_mul_abs_im_mul_relativeLength
    (s : ℂ) (K N : ℕ) :
    etaPairFrameBlockSpan s K N ≤
      2 * |s.im| *
        ((N : ℝ) / etaPairFrameLeftEndpoint K) := by
  have ha : 0 < etaPairFrameLeftEndpoint K :=
    etaPairFrameLeftEndpoint_pos K
  have hb : 0 < etaPairFrameLeftEndpoint (K + N) :=
    etaPairFrameLeftEndpoint_pos (K + N)
  have hstep :
      etaPairFrameLeftEndpoint (K + N) =
        etaPairFrameLeftEndpoint K + 2 * (N : ℝ) := by
    unfold etaPairFrameLeftEndpoint
    push_cast
    ring
  have hlog :
      Real.log
          (etaPairFrameLeftEndpoint (K + N) /
            etaPairFrameLeftEndpoint K) ≤
        etaPairFrameLeftEndpoint (K + N) /
            etaPairFrameLeftEndpoint K - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hb ha)
  have hratio :
      etaPairFrameLeftEndpoint (K + N) /
          etaPairFrameLeftEndpoint K - 1 =
        2 * (N : ℝ) / etaPairFrameLeftEndpoint K := by
    rw [hstep]
    field_simp [ha.ne']
    ring
  rw [hratio] at hlog
  rw [etaPairFrameBlockSpan_eq,
    ← Real.log_div hb.ne' ha.ne']
  calc
    |s.im| *
        Real.log
          (etaPairFrameLeftEndpoint (K + N) /
            etaPairFrameLeftEndpoint K) ≤
        |s.im| *
          (2 * (N : ℝ) / etaPairFrameLeftEndpoint K) :=
      mul_le_mul_of_nonneg_left hlog (abs_nonneg s.im)
    _ =
        2 * |s.im| *
          ((N : ℝ) / etaPairFrameLeftEndpoint K) := by
      ring

/-- Increasing the block length can only increase its total frame span. -/
theorem etaPairFrameBlockSpan_mono_length
    (s : ℂ) (K : ℕ) {j N : ℕ} (hjN : j ≤ N) :
    etaPairFrameBlockSpan s K j ≤
      etaPairFrameBlockSpan s K N := by
  have hendpoint :
      etaPairFrameLeftEndpoint (K + j) ≤
        etaPairFrameLeftEndpoint (K + N) := by
    unfold etaPairFrameLeftEndpoint
    exact_mod_cast (by omega : 2 * (K + j) + 1 ≤ 2 * (K + N) + 1)
  rw [etaPairFrameBlockSpan_eq, etaPairFrameBlockSpan_eq]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg s.im)
  exact
    sub_le_sub_right
      (Real.log_le_log
        (etaPairFrameLeftEndpoint_pos (K + j)) hendpoint)
      _

namespace EtaPairGrowingBlockSchedule

/-- The scheduled block lengths are eventually nonzero. -/
theorem eventually_blockLength_pos
    (S : EtaPairGrowingBlockSchedule) :
    ∀ᶠ K : ℕ in atTop, 0 < S.blockLength K := by
  have hge : ∀ᶠ K : ℕ in atTop, 1 ≤ S.blockLength K :=
    (tendsto_atTop.1 S.blockLength_tendsto_atTop) 1
  filter_upwards [hge] with K hK
  omega

/--
Every sublinear growing schedule has total block-frame span tending to zero.
-/
theorem frameBlockSpan_tendsto_zero
    (S : EtaPairGrowingBlockSchedule) (s : ℂ) :
    Tendsto
      (fun K : ℕ =>
        etaPairFrameBlockSpan s K (S.blockLength K))
      atTop (nhds 0) := by
  have hupper :
      Tendsto
        (fun K : ℕ =>
          2 * |s.im| *
            ((S.blockLength K : ℝ) /
              etaPairFrameLeftEndpoint K))
        atTop (nhds 0) := by
    simpa [mul_assoc] using
      S.relativeLength_tendsto_zero.const_mul (2 * |s.im|)
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hupper
      (Eventually.of_forall fun K =>
        etaPairFrameBlockSpan_nonneg s K (S.blockLength K))
      (Eventually.of_forall fun K =>
        etaPairFrameBlockSpan_le_two_mul_abs_im_mul_relativeLength
          s K (S.blockLength K))

/-- The full scheduled block span is eventually at most one radian. -/
theorem eventually_frameBlockSpan_le_one
    (S : EtaPairGrowingBlockSchedule) (s : ℂ) :
    ∀ᶠ K : ℕ in atTop,
      etaPairFrameBlockSpan s K (S.blockLength K) ≤ 1 := by
  have hlt :=
    (S.frameBlockSpan_tendsto_zero s).eventually_lt_const
      (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hlt] with K hK
  exact hK.le

/-- Every initial subblock of a late scheduled block also has span at most one. -/
theorem eventually_all_subblockSpan_le_one
    (S : EtaPairGrowingBlockSchedule) (s : ℂ) :
    ∀ᶠ K : ℕ in atTop,
      ∀ j : ℕ, j ≤ S.blockLength K →
        etaPairFrameBlockSpan s K j ≤ 1 := by
  filter_upwards [S.eventually_frameBlockSpan_le_one s] with K hK
  intro j hj
  exact (etaPairFrameBlockSpan_mono_length s K hj).trans hK

/--
At a nonreal point, the full scheduled block eventually satisfies the precise
small-angle inequality used by the margin-domination argument.
-/
theorem eventually_eight_mul_normCoefficient_mul_frameBlockSpan_lt_abs_im
    (S : EtaPairGrowingBlockSchedule)
    {s : ℂ} (him : s.im ≠ 0) :
    ∀ᶠ K : ℕ in atTop,
      8 * etaCriticalMirrorDefectPairNormCoefficient s *
          etaPairFrameBlockSpan s K (S.blockLength K) <
        |s.im| := by
  have hscaled :
      Tendsto
        (fun K : ℕ =>
          8 * etaCriticalMirrorDefectPairNormCoefficient s *
            etaPairFrameBlockSpan s K (S.blockLength K))
        atTop (nhds 0) := by
    simpa [mul_assoc] using
      (S.frameBlockSpan_tendsto_zero s).const_mul
        (8 * etaCriticalMirrorDefectPairNormCoefficient s)
  exact hscaled.eventually_lt_const (abs_pos.mpr him)

/--
The same strict small-angle inequality holds uniformly for every initial
subblock of the scheduled growing block.
-/
theorem eventually_all_subblock_eight_mul_normCoefficient_mul_span_lt_abs_im
    (S : EtaPairGrowingBlockSchedule)
    {s : ℂ} (him : s.im ≠ 0) :
    ∀ᶠ K : ℕ in atTop,
      ∀ j : ℕ, j ≤ S.blockLength K →
        8 * etaCriticalMirrorDefectPairNormCoefficient s *
            etaPairFrameBlockSpan s K j <
          |s.im| := by
  filter_upwards
    [S.eventually_eight_mul_normCoefficient_mul_frameBlockSpan_lt_abs_im him]
      with K hK
  intro j hj
  have hmono :
      8 * etaCriticalMirrorDefectPairNormCoefficient s *
          etaPairFrameBlockSpan s K j ≤
        8 * etaCriticalMirrorDefectPairNormCoefficient s *
          etaPairFrameBlockSpan s K (S.blockLength K) :=
    mul_le_mul_of_nonneg_left
      (etaPairFrameBlockSpan_mono_length s K hj)
      (by positivity)
  exact hmono.trans_lt hK

end EtaPairGrowingBlockSchedule

end DkMath.RH.CFBRCProjection
