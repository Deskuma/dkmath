/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameGrowingBlockGeometry

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameGrowingBlockGeometry"

set_option linter.style.longLine false

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameGrowingBlockGeometry

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

example (s : ℂ) (K N : ℕ) :
    etaPairFrameBlockSpan s K N ≤
      2 * |s.im| *
        ((N : ℝ) / etaPairFrameLeftEndpoint K) :=
  etaPairFrameBlockSpan_le_two_mul_abs_im_mul_relativeLength s K N

example (s : ℂ) (K : ℕ) {j N : ℕ} (hjN : j ≤ N) :
    etaPairFrameBlockSpan s K j ≤
      etaPairFrameBlockSpan s K N :=
  etaPairFrameBlockSpan_mono_length s K hjN

example (S : EtaPairGrowingBlockSchedule) :
    Tendsto S.blockLength atTop atTop :=
  S.blockLength_tendsto_atTop

example (S : EtaPairGrowingBlockSchedule) :
    ∀ᶠ K : ℕ in atTop, 0 < S.blockLength K :=
  S.eventually_blockLength_pos

example (S : EtaPairGrowingBlockSchedule) (s : ℂ) :
    Tendsto
      (fun K : ℕ =>
        etaPairFrameBlockSpan s K (S.blockLength K))
      atTop (nhds 0) :=
  S.frameBlockSpan_tendsto_zero s

example (S : EtaPairGrowingBlockSchedule) (s : ℂ) :
    ∀ᶠ K : ℕ in atTop,
      ∀ j : ℕ, j ≤ S.blockLength K →
        etaPairFrameBlockSpan s K j ≤ 1 :=
  S.eventually_all_subblockSpan_le_one s

example (S : EtaPairGrowingBlockSchedule)
    {s : ℂ} (him : s.im ≠ 0) :
    ∀ᶠ K : ℕ in atTop,
      ∀ j : ℕ, j ≤ S.blockLength K →
        8 * etaCriticalMirrorDefectPairNormCoefficient s *
            etaPairFrameBlockSpan s K j <
          |s.im| :=
  S.eventually_all_subblock_eight_mul_normCoefficient_mul_span_lt_abs_im him

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameGrowingBlockGeometry
