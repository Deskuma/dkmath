/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameAbelCorrectionTailBound
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameMovingProjectionTailMargin"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped BigOperators Topology

/-- Lift one eventual pair-index statement uniformly beyond every late start. -/
private theorem eventually_all_nat_add_movingProjectionTailMargin
    {P : ℕ → Prop}
    (hP : ∀ᶠ k : ℕ in atTop, P k) :
    ∀ᶠ K : ℕ in atTop, ∀ j : ℕ, P (K + j) := by
  rcases eventually_atTop.1 hP with ⟨K₀, hK₀⟩
  exact eventually_atTop.2 ⟨K₀, by
    intro K hK j
    exact hK₀ (K + j) (by omega)⟩

/--
A moving-frame projection tail splits into its next finite projection block
and the projection tail beginning after that block.
-/
theorem etaCriticalMirrorRotatedDefectProjectionTail_eq_block_add_tail
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (K N : ℕ) :
    etaCriticalMirrorRotatedDefectProjectionTail K s =
      (Finset.range N).sum
          (fun j : ℕ =>
            etaCriticalMirrorRotatedDefectPairProjection s (K + j)) +
        etaCriticalMirrorRotatedDefectProjectionTail (K + N) s := by
  have hsum :=
    summable_etaCriticalMirrorRotatedDefectPairProjection hs
  have hshift :
      Summable
        (fun j : ℕ =>
          etaCriticalMirrorRotatedDefectPairProjection s (j + K)) :=
    (summable_nat_add_iff K).2 hsum
  have hsplit := hshift.sum_add_tsum_nat_add N
  simpa [etaCriticalMirrorRotatedDefectProjectionTail,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsplit.symm

namespace EtaPairGrowingBlockSchedule

/--
Right of the critical line, the complete moving projection tail eventually
strictly dominates the full explicit right margin of every scheduled block.
-/
theorem eventually_rightBlockMarginSum_lt_rotatedDefectProjectionTail
    (S : EtaPairGrowingBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorRightBlockMarginSum
          s K (S.blockLength K) <
        etaCriticalMirrorRotatedDefectProjectionTail K s := by
  have hlocal :=
    eventually_all_nat_add_movingProjectionTailMargin
      (eventually_etaCriticalMirrorRightPairMargin_le_rotatedDefectPairProjection
        hs him hre)
  have htail :=
    eventually_all_nat_add_movingProjectionTailMargin
      (eventually_etaCriticalMirrorRotatedDefectProjectionTail_pos_of_half_lt_re
        hs him hre)
  filter_upwards [hlocal, htail] with K hlocalK htailK
  rw [etaCriticalMirrorRotatedDefectProjectionTail_eq_block_add_tail
    hs K (S.blockLength K)]
  unfold etaCriticalMirrorRightBlockMarginSum
  have hsum :
      (Finset.range (S.blockLength K)).sum
          (fun j : ℕ =>
            etaCriticalMirrorRightPairMargin s (K + j)) ≤
        (Finset.range (S.blockLength K)).sum
          (fun j : ℕ =>
            etaCriticalMirrorRotatedDefectPairProjection s (K + j)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact hlocalK j
  linarith [htailK (S.blockLength K)]

/--
Left of the critical line, the negated moving projection tail eventually
strictly dominates the full explicit left margin of every scheduled block.
-/
theorem eventually_leftBlockMarginSum_lt_neg_rotatedDefectProjectionTail
    (S : EtaPairGrowingBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorLeftBlockMarginSum
          s K (S.blockLength K) <
        -etaCriticalMirrorRotatedDefectProjectionTail K s := by
  have hlocal :=
    eventually_all_nat_add_movingProjectionTailMargin
      (eventually_etaCriticalMirrorLeftPairMargin_le_neg_rotatedDefectPairProjection
        hs him hre)
  have htail :=
    eventually_all_nat_add_movingProjectionTailMargin
      (eventually_etaCriticalMirrorRotatedDefectProjectionTail_neg_of_re_lt_half
        hs him hre)
  filter_upwards [hlocal, htail] with K hlocalK htailK
  rw [etaCriticalMirrorRotatedDefectProjectionTail_eq_block_add_tail
    hs K (S.blockLength K)]
  unfold etaCriticalMirrorLeftBlockMarginSum
  have hsum :
      (Finset.range (S.blockLength K)).sum
          (fun j : ℕ =>
            etaCriticalMirrorLeftPairMargin s (K + j)) ≤
        -(Finset.range (S.blockLength K)).sum
          (fun j : ℕ =>
            etaCriticalMirrorRotatedDefectPairProjection s (K + j)) := by
    calc
      (Finset.range (S.blockLength K)).sum
          (fun j : ℕ =>
            etaCriticalMirrorLeftPairMargin s (K + j)) ≤
        (Finset.range (S.blockLength K)).sum
          (fun j : ℕ =>
            -etaCriticalMirrorRotatedDefectPairProjection s (K + j)) := by
        apply Finset.sum_le_sum
        intro j hj
        exact hlocalK j
      _ =
        -(Finset.range (S.blockLength K)).sum
          (fun j : ℕ =>
            etaCriticalMirrorRotatedDefectPairProjection s (K + j)) := by
        simp
  linarith [htailK (S.blockLength K)]

/-- The scheduled right block margins eventually dominate the Abel correction bound. -/
def RightBlockMarginDominatesAbelCorrection
    (S : EtaPairGrowingBlockSchedule) (s : ℂ) : Prop :=
  ∀ᶠ K : ℕ in atTop,
    etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound s (K - 1) <
      etaCriticalMirrorRightBlockMarginSum s K (S.blockLength K)

/-- The scheduled left block margins eventually dominate the Abel correction bound. -/
def LeftBlockMarginDominatesAbelCorrection
    (S : EtaPairGrowingBlockSchedule) (s : ℂ) : Prop :=
  ∀ᶠ K : ℕ in atTop,
    etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound s (K - 1) <
      etaCriticalMirrorLeftBlockMarginSum s K (S.blockLength K)

/-- A right block-margin comparison supplies the earlier Abel domination gate. -/
theorem rightAbelCorrectionTailDominated_of_blockMargin
    (S : EtaPairGrowingBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re)
    (hdom : S.RightBlockMarginDominatesAbelCorrection s) :
    RightAbelCorrectionTailDominated s := by
  have hmargin :=
    S.eventually_rightBlockMarginSum_lt_rotatedDefectProjectionTail
      hs him hre
  filter_upwards [hdom, hmargin] with K hdomK hmarginK
  exact hdomK.trans hmarginK

/-- A left block-margin comparison supplies the earlier Abel domination gate. -/
theorem leftAbelCorrectionTailDominated_of_blockMargin
    (S : EtaPairGrowingBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2)
    (hdom : S.LeftBlockMarginDominatesAbelCorrection s) :
    LeftAbelCorrectionTailDominated s := by
  have hmargin :=
    S.eventually_leftBlockMarginSum_lt_neg_rotatedDefectProjectionTail
      hs him hre
  filter_upwards [hdom, hmargin] with K hdomK hmarginK
  exact hdomK.trans hmarginK

/-- Right block-margin domination forces the predecessor-frame whole tail positive. -/
theorem eventually_predecessorFrameWholeTailProjection_pos_of_rightBlockMarginDomination
    (S : EtaPairGrowingBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re)
    (hdom : S.RightBlockMarginDominatesAbelCorrection s) :
    ∀ᶠ K : ℕ in atTop,
      0 < etaCriticalMirrorPredecessorFrameWholeTailProjection K s :=
  eventually_predecessorFrameWholeTailProjection_pos_of_rightAbelCorrectionTailDominated
    hs him hre
    (S.rightAbelCorrectionTailDominated_of_blockMargin hs him hre hdom)

/-- Left block-margin domination forces the predecessor-frame whole tail negative. -/
theorem eventually_predecessorFrameWholeTailProjection_neg_of_leftBlockMarginDomination
    (S : EtaPairGrowingBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2)
    (hdom : S.LeftBlockMarginDominatesAbelCorrection s) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorPredecessorFrameWholeTailProjection K s < 0 :=
  eventually_predecessorFrameWholeTailProjection_neg_of_leftAbelCorrectionTailDominated
    hs him hre
    (S.leftAbelCorrectionTailDominated_of_blockMargin hs him hre hdom)

end EtaPairGrowingBlockSchedule

end DkMath.RH.CFBRCProjection
