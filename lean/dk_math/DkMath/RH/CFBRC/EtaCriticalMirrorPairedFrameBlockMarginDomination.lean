/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorDefectPairNormMarginComparison
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameBlockProjection
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameBlockMarginDomination"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-- Shift an eventual natural-number statement by one fixed offset. -/
private theorem eventually_nat_add_const_blockMargin
    {P : ℕ → Prop} (j : ℕ)
    (hP : ∀ᶠ k : ℕ in atTop, P k) :
    ∀ᶠ K : ℕ in atTop, P (K + j) := by
  rcases eventually_atTop.1 hP with ⟨K₀, hK₀⟩
  exact eventually_atTop.2 ⟨K₀, by
    intro K hK
    exact hK₀ (K + j) (by omega)⟩

/--
Pure algebraic comparison used to turn a scaled norm bound and a sufficiently
small frame angle into strict domination by a positive margin.
-/
private theorem transferError_lt_margin_of_scaledNorm_le
    {t C S n M : ℝ}
    (ht : t ≠ 0)
    (hS : 0 ≤ S)
    (hM : 0 < M)
    (hscaled : (t ^ 2 / 4) * n ≤ C * M)
    (hangle : 8 * C * S < |t|) :
    2 * |t| * S * n < M := by
  have habsPos : 0 < |t| := abs_pos.mpr ht
  have habsSq : |t| ^ 2 = t ^ 2 := sq_abs t
  have hscaled' :
      (|t| ^ 2 / 4) * n ≤ C * M := by
    rw [habsSq]
    exact hscaled
  have hmul :
      8 * S * ((|t| ^ 2 / 4) * n) ≤
        8 * S * (C * M) :=
    mul_le_mul_of_nonneg_left hscaled'
      (mul_nonneg (by norm_num) hS)
  have hangleM :
      (8 * C * S) * M < |t| * M :=
    mul_lt_mul_of_pos_right hangle hM
  have hcombined :
      |t| * (2 * |t| * S * n) < |t| * M := by
    calc
      |t| * (2 * |t| * S * n) =
          8 * S * ((|t| ^ 2 / 4) * n) := by ring
      _ ≤ 8 * S * (C * M) := hmul
      _ = (8 * C * S) * M := by ring
      _ < |t| * M := hangleM
  exact (mul_lt_mul_left habsPos).mp hcombined

/-- Every fixed-offset late block eventually has span at most one. -/
theorem eventually_etaPairFrameBlockSpan_le_one
    (s : ℂ) (j : ℕ) :
    ∀ᶠ K : ℕ in atTop,
      etaPairFrameBlockSpan s K j ≤ 1 := by
  have hlt :=
    (etaPairFrameBlockSpan_tendsto_zero s j).eventually_lt_const
      (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hlt] with K hK
  exact hK.le

/--
For a nonreal point and one fixed offset, the logarithmic block span eventually
satisfies the exact angle condition needed to dominate frame-transfer error.
-/
theorem eventually_eight_mul_normCoefficient_mul_blockSpan_lt_abs_im
    {s : ℂ} (him : s.im ≠ 0) (j : ℕ) :
    ∀ᶠ K : ℕ in atTop,
      8 * etaCriticalMirrorDefectPairNormCoefficient s *
          etaPairFrameBlockSpan s K j <
        |s.im| := by
  have hscaled :
      Tendsto
        (fun K : ℕ =>
          8 * etaCriticalMirrorDefectPairNormCoefficient s *
            etaPairFrameBlockSpan s K j)
        atTop (nhds 0) := by
    simpa [mul_assoc] using
      (etaPairFrameBlockSpan_tendsto_zero s j).const_mul
        (8 * etaCriticalMirrorDefectPairNormCoefficient s)
  exact hscaled.eventually_lt_const (abs_pos.mpr him)

/--
Right of the critical line, the block-frame transfer error is eventually
strictly smaller than the explicit positive pair margin at every fixed offset.
-/
theorem eventually_etaCriticalMirrorBlockTransferError_lt_rightPairMargin
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re)
    (j : ℕ) :
    ∀ᶠ K : ℕ in atTop,
      2 * |s.im| * etaPairFrameBlockSpan s K j *
          ‖etaCriticalMirrorDefectPairTerm s (K + j)‖ <
        etaCriticalMirrorRightPairMargin s (K + j) := by
  have hnorm :=
    eventually_nat_add_const_blockMargin j
      (eventually_scaled_norm_etaCriticalMirrorDefectPairTerm_le_rightPairMargin
        hs hre)
  have hangle :=
    eventually_eight_mul_normCoefficient_mul_blockSpan_lt_abs_im
      him j
  filter_upwards [hnorm, hangle] with K hnormK hangleK
  exact
    transferError_lt_margin_of_scaledNorm_le
      him
      (etaPairFrameBlockSpan_nonneg s K j)
      (etaCriticalMirrorRightPairMargin_pos him (K + j))
      hnormK hangleK

/--
Left of the critical line, the same block-frame transfer error is eventually
strictly smaller than the explicit negative pair margin at every fixed offset.
-/
theorem eventually_etaCriticalMirrorBlockTransferError_lt_leftPairMargin
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2)
    (j : ℕ) :
    ∀ᶠ K : ℕ in atTop,
      2 * |s.im| * etaPairFrameBlockSpan s K j *
          ‖etaCriticalMirrorDefectPairTerm s (K + j)‖ <
        etaCriticalMirrorLeftPairMargin s (K + j) := by
  have hnorm :=
    eventually_nat_add_const_blockMargin j
      (eventually_scaled_norm_etaCriticalMirrorDefectPairTerm_le_leftPairMargin
        hs hre)
  have hangle :=
    eventually_eight_mul_normCoefficient_mul_blockSpan_lt_abs_im
      him j
  filter_upwards [hnorm, hangle] with K hnormK hangleK
  exact
    transferError_lt_margin_of_scaledNorm_le
      him
      (etaPairFrameBlockSpan_nonneg s K j)
      (etaCriticalMirrorLeftPairMargin_pos him (K + j))
      hnormK hangleK

/--
Right of the critical line, every fixed-offset pair is eventually positive in
the single frame chosen at the beginning of its finite block.
-/
theorem eventually_etaCriticalMirrorBlockStartDefectPairProjection_pos_of_half_lt_re
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re)
    (j : ℕ) :
    ∀ᶠ K : ℕ in atTop,
      0 < etaCriticalMirrorBlockStartDefectPairProjection s K j := by
  have hspan := eventually_etaPairFrameBlockSpan_le_one s j
  have herror :=
    eventually_etaCriticalMirrorBlockTransferError_lt_rightPairMargin
      hs him hre j
  have hlocal :=
    eventually_nat_add_const_blockMargin j
      (eventually_etaCriticalMirrorRightPairMargin_le_rotatedDefectPairProjection
        hs him hre)
  filter_upwards [hspan, herror, hlocal] with K hspanK herrorK hlocalK
  apply
    etaCriticalMirrorBlockStartDefectPairProjection_pos_of_local_margin
      s K j hspanK
  exact herrorK.trans_le hlocalK

/--
Left of the critical line, every fixed-offset pair is eventually negative in
the single frame chosen at the beginning of its finite block.
-/
theorem eventually_etaCriticalMirrorBlockStartDefectPairProjection_neg_of_re_lt_half
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2)
    (j : ℕ) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorBlockStartDefectPairProjection s K j < 0 := by
  have hspan := eventually_etaPairFrameBlockSpan_le_one s j
  have herror :=
    eventually_etaCriticalMirrorBlockTransferError_lt_leftPairMargin
      hs him hre j
  have hlocal :=
    eventually_nat_add_const_blockMargin j
      (eventually_etaCriticalMirrorLeftPairMargin_le_neg_rotatedDefectPairProjection
        hs him hre)
  filter_upwards [hspan, herror, hlocal] with K hspanK herrorK hlocalK
  apply
    etaCriticalMirrorBlockStartDefectPairProjection_neg_of_local_margin
      s K j hspanK
  exact herrorK.trans_le hlocalK

end DkMath.RH.CFBRCProjection
