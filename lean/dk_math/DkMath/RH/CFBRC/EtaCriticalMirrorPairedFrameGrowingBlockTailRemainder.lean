/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameGrowingBlockQuantitativeCertificate
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedTailBound
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameGrowingBlockTailRemainder"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped BigOperators Topology

/-- The part of the paired defect tail lying strictly after one indexed block. -/
noncomputable def etaCriticalMirrorBlockStartRotatedResidualTail
    (s : ℂ) (K N : ℕ) : ℂ :=
  etaPairBaseRotation s K *
    etaCriticalMirrorDefectPairTail (K + N) s

/-- Signed vertical projection of the residual tail in the block-start frame. -/
noncomputable def etaCriticalMirrorBlockStartResidualTailProjection
    (s : ℂ) (K N : ℕ) : ℝ :=
  etaCriticalMirrorSignedVerticalProjection s
    (etaCriticalMirrorBlockStartRotatedResidualTail s K N)

/-- The complete paired tail beginning at `K`, rotated into the frame at `K`. -/
noncomputable def etaCriticalMirrorBlockStartRotatedWholeTail
    (s : ℂ) (K : ℕ) : ℂ :=
  etaPairBaseRotation s K *
    etaCriticalMirrorDefectPairTail K s

/-- Signed vertical projection of the complete paired tail in its start frame. -/
noncomputable def etaCriticalMirrorBlockStartWholeTailProjection
    (s : ℂ) (K : ℕ) : ℝ :=
  etaCriticalMirrorSignedVerticalProjection s
    (etaCriticalMirrorBlockStartRotatedWholeTail s K)

/-- Explicit norm majorant for the paired defect tail beginning at `L`. -/
noncomputable def etaCriticalMirrorDefectPairTailPowerBound
    (s : ℂ) (L : ℕ) : ℝ :=
  ‖criticalMirror s‖ *
      (((L : ℝ) ^ (-(criticalMirror s).re)) /
        (criticalMirror s).re) +
    ‖s‖ * (((L : ℝ) ^ (-s.re)) / s.re)

/-- Explicit projected residual-tail majorant in one block-start frame. -/
noncomputable def etaCriticalMirrorBlockStartResidualTailPowerBound
    (s : ℂ) (K N : ℕ) : ℝ :=
  |s.im| *
    etaCriticalMirrorDefectPairTailPowerBound s (K + N)

/-- A paired tail splits exactly into its next finite block and later tail. -/
theorem etaCriticalMirrorDefectPairTail_eq_block_add_tail
    {s : ℂ} (hsum : Summable (etaCriticalMirrorDefectPairTerm s))
    (K N : ℕ) :
    etaCriticalMirrorDefectPairTail K s =
      (Finset.range N).sum
          (fun j : ℕ => etaCriticalMirrorDefectPairTerm s (K + j)) +
        etaCriticalMirrorDefectPairTail (K + N) s := by
  have hshift :
      Summable
        (fun j : ℕ => etaCriticalMirrorDefectPairTerm s (j + K)) :=
    (summable_nat_add_iff K).2 hsum
  have hsplit := hshift.sum_add_tsum_nat_add N
  simpa [etaCriticalMirrorDefectPairTail, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using hsplit.symm

/-- In the block-start frame, the complete tail is block plus residual tail. -/
theorem etaCriticalMirrorBlockStartRotatedWholeTail_eq_block_add_residual
    {s : ℂ} (hsum : Summable (etaCriticalMirrorDefectPairTerm s))
    (K N : ℕ) :
    etaCriticalMirrorBlockStartRotatedWholeTail s K =
      etaCriticalMirrorBlockStartRotatedDefectBlockTerm s K N +
        etaCriticalMirrorBlockStartRotatedResidualTail s K N := by
  unfold etaCriticalMirrorBlockStartRotatedWholeTail
  unfold etaCriticalMirrorBlockStartRotatedResidualTail
  rw [etaCriticalMirrorDefectPairTail_eq_block_add_tail hsum K N,
    mul_add, Finset.mul_sum]
  unfold etaCriticalMirrorBlockStartRotatedDefectBlockTerm
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro j hj
    rfl
  · rfl

/-- Signed projection preserves the preceding block-plus-residual decomposition. -/
theorem etaCriticalMirrorBlockStartWholeTailProjection_eq_block_add_residual
    {s : ℂ} (hsum : Summable (etaCriticalMirrorDefectPairTerm s))
    (K N : ℕ) :
    etaCriticalMirrorBlockStartWholeTailProjection s K =
      etaCriticalMirrorBlockStartDefectBlockProjection s K N +
        etaCriticalMirrorBlockStartResidualTailProjection s K N := by
  unfold etaCriticalMirrorBlockStartWholeTailProjection
  unfold etaCriticalMirrorBlockStartDefectBlockProjection
  unfold etaCriticalMirrorBlockStartResidualTailProjection
  rw [etaCriticalMirrorBlockStartRotatedWholeTail_eq_block_add_residual
    hsum K N]
  unfold etaCriticalMirrorSignedVerticalProjection
  simp
  ring

/-- Rotation by the block-start frame does not enlarge residual-tail projection. -/
theorem abs_etaCriticalMirrorBlockStartResidualTailProjection_le
    (s : ℂ) (K N : ℕ) :
    |etaCriticalMirrorBlockStartResidualTailProjection s K N| ≤
      |s.im| *
        ‖etaCriticalMirrorDefectPairTail (K + N) s‖ := by
  unfold etaCriticalMirrorBlockStartResidualTailProjection
  unfold etaCriticalMirrorBlockStartRotatedResidualTail
  unfold etaCriticalMirrorSignedVerticalProjection
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg s.im)
  calc
    |(etaPairBaseRotation s K *
        etaCriticalMirrorDefectPairTail (K + N) s).im| ≤
        ‖etaPairBaseRotation s K *
          etaCriticalMirrorDefectPairTail (K + N) s‖ :=
      Complex.abs_im_le_norm _
    _ = ‖etaCriticalMirrorDefectPairTail (K + N) s‖ := by
      rw [norm_mul, norm_etaPairBaseRotation, one_mul]

/-- The existing p-series tail estimate written through the named power bound. -/
theorem norm_etaCriticalMirrorDefectPairTail_le_powerBound
    {s : ℂ} (hs : 0 < s.re) (hm : 0 < (criticalMirror s).re)
    {L : ℕ} (hL : 1 ≤ L) :
    ‖etaCriticalMirrorDefectPairTail L s‖ ≤
      etaCriticalMirrorDefectPairTailPowerBound s L := by
  simpa [etaCriticalMirrorDefectPairTailPowerBound] using
    norm_etaCriticalMirrorDefectPairTail_le hs hm hL

/-- The projected residual tail is bounded by its explicit power majorant. -/
theorem abs_etaCriticalMirrorBlockStartResidualTailProjection_le_powerBound
    {s : ℂ} (hs : 0 < s.re) (hm : 0 < (criticalMirror s).re)
    {K N : ℕ} (hKN : 1 ≤ K + N) :
    |etaCriticalMirrorBlockStartResidualTailProjection s K N| ≤
      etaCriticalMirrorBlockStartResidualTailPowerBound s K N := by
  unfold etaCriticalMirrorBlockStartResidualTailPowerBound
  exact
    (abs_etaCriticalMirrorBlockStartResidualTailProjection_le s K N).trans
      (mul_le_mul_of_nonneg_left
        (norm_etaCriticalMirrorDefectPairTail_le_powerBound hs hm hKN)
        (abs_nonneg s.im))

namespace EtaPairGrowingBlockSchedule

/-- Along every schedule, the projected residual tail eventually obeys the power bound. -/
theorem eventually_abs_blockStartResidualTailProjection_le_powerBound
    (S : EtaPairGrowingBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    ∀ᶠ K : ℕ in atTop,
      |etaCriticalMirrorBlockStartResidualTailProjection
          s K (S.blockLength K)| ≤
        etaCriticalMirrorBlockStartResidualTailPowerBound
          s K (S.blockLength K) := by
  filter_upwards [eventually_atTop.2 ⟨1, fun K hK => hK⟩] with K hK
  apply
    abs_etaCriticalMirrorBlockStartResidualTailProjection_le_powerBound
      (nontrivialRiemannZetaZero_re_pos hs)
      (criticalMirror_re_pos_of_nontrivialRiemannZetaZero hs)
  omega

/-- Explicit right-side condition saying the residual tail is below half block margin. -/
def RightResidualTailDominated
    (S : EtaPairGrowingBlockSchedule) (s : ℂ) : Prop :=
  ∀ᶠ K : ℕ in atTop,
    etaCriticalMirrorBlockStartResidualTailPowerBound
        s K (S.blockLength K) <
      (1 : ℝ) / 2 *
        etaCriticalMirrorRightBlockMarginSum
          s K (S.blockLength K)

/-- Explicit left-side condition saying the residual tail is below half block margin. -/
def LeftResidualTailDominated
    (S : EtaPairGrowingBlockSchedule) (s : ℂ) : Prop :=
  ∀ᶠ K : ℕ in atTop,
    etaCriticalMirrorBlockStartResidualTailPowerBound
        s K (S.blockLength K) <
      (1 : ℝ) / 2 *
        etaCriticalMirrorLeftBlockMarginSum
          s K (S.blockLength K)

/-- Right residual domination forces the whole tail into the positive half-plane. -/
theorem eventually_blockStartWholeTailProjection_pos_of_rightResidualTailDominated
    (S : EtaPairGrowingBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re)
    (hdom : S.RightResidualTailDominated s) :
    ∀ᶠ K : ℕ in atTop,
      0 < etaCriticalMirrorBlockStartWholeTailProjection s K := by
  have hblock :=
    S.eventually_half_rightBlockMarginSum_lt_blockStartProjection
      hs him hre
  have hres :=
    S.eventually_abs_blockStartResidualTailProjection_le_powerBound hs
  filter_upwards [hblock, hres, hdom] with K hblockK hresK hdomK
  have habs :
      |etaCriticalMirrorBlockStartResidualTailProjection
          s K (S.blockLength K)| <
        (1 : ℝ) / 2 *
          etaCriticalMirrorRightBlockMarginSum
            s K (S.blockLength K) :=
    hresK.trans_lt hdomK
  have hlower := neg_lt_of_abs_lt habs
  rw [etaCriticalMirrorBlockStartWholeTailProjection_eq_block_add_residual
    (summable_etaCriticalMirrorDefectPairTerm_of_nontrivialRiemannZetaZero hs)
    K (S.blockLength K)]
  linarith

/-- Left residual domination forces the whole tail into the negative half-plane. -/
theorem eventually_blockStartWholeTailProjection_neg_of_leftResidualTailDominated
    (S : EtaPairGrowingBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2)
    (hdom : S.LeftResidualTailDominated s) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorBlockStartWholeTailProjection s K < 0 := by
  have hblock :=
    S.eventually_half_leftBlockMarginSum_lt_neg_blockStartProjection
      hs him hre
  have hres :=
    S.eventually_abs_blockStartResidualTailProjection_le_powerBound hs
  filter_upwards [hblock, hres, hdom] with K hblockK hresK hdomK
  have habs :
      |etaCriticalMirrorBlockStartResidualTailProjection
          s K (S.blockLength K)| <
        (1 : ℝ) / 2 *
          etaCriticalMirrorLeftBlockMarginSum
            s K (S.blockLength K) :=
    hresK.trans_lt hdomK
  have hupper := lt_of_abs_lt habs
  rw [etaCriticalMirrorBlockStartWholeTailProjection_eq_block_add_residual
    (summable_etaCriticalMirrorDefectPairTerm_of_nontrivialRiemannZetaZero hs)
    K (S.blockLength K)]
  linarith

end EtaPairGrowingBlockSchedule

end DkMath.RH.CFBRCProjection
