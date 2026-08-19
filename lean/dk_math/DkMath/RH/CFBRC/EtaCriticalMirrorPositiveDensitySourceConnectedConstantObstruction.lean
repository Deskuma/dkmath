/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPositiveDensityNormalizedConstantObstructionAudit
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameGrowingBlockTailRemainder
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedConstantAudit
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFramePositiveDensityRotationLimit
import Mathlib.Tactic

/-!
# ZDI-010: source-connected positive-density constant obstruction

This module connects the ZDI-009 scalar obstruction to the existing
positive-density schedule, residual-majorant, and block-margin objects.  It
does not estimate the exact oscillatory Eta tail or construct a fixed
block-start projection transport theorem.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

namespace EtaPairPositiveDensityBlockSchedule

/-!
The scheduled residual starts at the index `K + S.blockLength K`, whereas
the positive-density margin is normalized by the pair-left endpoint at `K`.
This helper records the resulting source-derived index ratio.
-/

/-- The scheduled tail index divided by the initial pair-left endpoint. -/
theorem blockStartIndexRatio_tendsto
    (S : EtaPairPositiveDensityBlockSchedule) :
    Tendsto
      (fun K : ℕ =>
        ((K + S.blockLength K : ℕ) : ℝ) /
          etaPairFrameLeftEndpoint K)
      atTop
      (nhds ((1 : ℝ) / 2 + S.density)) := by
  have hsmall0 :
      Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ))
        atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  have hsmall := hsmall0
  have hden :
      Tendsto
        (fun K : ℕ => (2 : ℝ) + (1 : ℝ) / (K : ℝ))
        atTop (nhds 2) := by
    simpa using tendsto_const_nhds.add hsmall
  have hinv := hden.inv₀ (by norm_num : (2 : ℝ) ≠ 0)
  have hinvHalf :
      Tendsto
        (fun K : ℕ => ((2 : ℝ) + (1 : ℝ) / (K : ℝ))⁻¹)
        atTop (nhds ((1 : ℝ) / 2)) := by
    simpa using hinv
  have hKratio :
      Tendsto
        (fun K : ℕ => (K : ℝ) / etaPairFrameLeftEndpoint K)
        atTop (nhds ((1 : ℝ) / 2)) := by
    refine hinvHalf.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with K hK
    have hKpos : 0 < (K : ℝ) := by exact_mod_cast hK
    unfold etaPairFrameLeftEndpoint
    norm_num [Nat.cast_add, Nat.cast_mul]
    field_simp [hKpos.ne']
  have hsum :
      Tendsto
        (fun K : ℕ =>
          (K : ℝ) / etaPairFrameLeftEndpoint K +
            (S.blockLength K : ℝ) / etaPairFrameLeftEndpoint K)
        atTop (nhds ((1 : ℝ) / 2 + S.density)) := by
    simpa using hKratio.add S.relativeLength_tendsto_density
  refine hsum.congr' ?_
  filter_upwards [] with K
  rw [Nat.cast_add]
  ring

/-- The reciprocal scheduled-index ratio tends to the positive-density scale. -/
theorem leftEndpoint_over_blockStartIndex_tendsto
    (S : EtaPairPositiveDensityBlockSchedule) :
    Tendsto
      (fun K : ℕ =>
        etaPairFrameLeftEndpoint K /
          ((K + S.blockLength K : ℕ) : ℝ))
      atTop
      (nhds (2 / (1 + 2 * S.density))) := by
  have hratio := S.blockStartIndexRatio_tendsto
  have hlimit : 0 < (1 : ℝ) / 2 + S.density := by
    linarith [S.density_pos]
  have hinv := hratio.inv₀ hlimit.ne'
  have hinv' :
      Tendsto
        (fun K : ℕ =>
          (((K + S.blockLength K : ℕ) : ℝ) /
            etaPairFrameLeftEndpoint K)⁻¹)
        atTop (nhds ((1 : ℝ) / 2 + S.density)⁻¹) := by
    simpa using hinv
  have hlimit' :
      ((1 : ℝ) / 2 + S.density)⁻¹ =
        2 / (1 + 2 * S.density) := by
    field_simp
  rw [hlimit'] at hinv'
  refine hinv'.congr' ?_
  filter_upwards [S.eventually_blockLength_pos] with K hN
  have hleft : 0 < etaPairFrameLeftEndpoint K :=
    etaPairFrameLeftEndpoint_pos K
  have hindex : 0 < ((K + S.blockLength K : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < K + S.blockLength K)
  field_simp [hleft.ne', hindex.ne']

/-!
The following two limits keep only the dominant nonnegative summand of the
existing residual power bound.  They are intentionally stated directly with
the source expressions rather than with a newly stored target constant.
-/

/-- Right-side dominant residual summand after pair-left normalization. -/
theorem right_normalizedDominantResidualPower_tendsto
    (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ} (hre : (1 : ℝ) / 2 < s.re) (hre1 : s.re < 1) :
    Tendsto
      (fun K : ℕ =>
        etaPairFrameLeftEndpoint K ^ (1 - s.re) *
          (|s.im| * ‖criticalMirror s‖ / (1 - s.re) *
            (((K + S.blockLength K : ℕ) : ℝ) ^ (-(1 - s.re)))))
      atTop
      (nhds
        (|s.im| * ‖criticalMirror s‖ / (1 - s.re) *
          (2 / (1 + 2 * S.density)) ^ (1 - s.re))) := by
  have hratio := S.leftEndpoint_over_blockStartIndex_tendsto
  have hratioPow := hratio.rpow_const
    (p := 1 - s.re)
    (Or.inl (by
      have ha : 0 < 1 + 2 * S.density := by linarith [S.density_pos]
      have : 0 < 2 / (1 + 2 * S.density) := div_pos (by norm_num) ha
      exact this.ne'))
  have hbase :
      Tendsto
        (fun K : ℕ =>
          |s.im| * ‖criticalMirror s‖ / (1 - s.re) *
            (etaPairFrameLeftEndpoint K /
              ((K + S.blockLength K : ℕ) : ℝ)) ^ (1 - s.re))
        atTop
        (nhds
          (|s.im| * ‖criticalMirror s‖ / (1 - s.re) *
            (2 / (1 + 2 * S.density)) ^ (1 - s.re))) := by
    simpa [mul_assoc] using
      (tendsto_const_nhds.mul hratioPow)
  refine hbase.congr' ?_
  filter_upwards [S.eventually_blockLength_pos] with K hN
  have hE : 0 < etaPairFrameLeftEndpoint K :=
    etaPairFrameLeftEndpoint_pos K
  have hL : 0 < ((K + S.blockLength K : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < K + S.blockLength K)
  rw [Real.div_rpow hE.le hL.le, Real.rpow_neg hL.le]
  field_simp [hE.ne', hL.ne']

/-- Left-side dominant residual summand after pair-left normalization. -/
theorem left_normalizedDominantResidualPower_tendsto
    (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ} (hre0 : 0 < s.re) (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (fun K : ℕ =>
        etaPairFrameLeftEndpoint K ^ s.re *
          (|s.im| * ‖s‖ / s.re *
            (((K + S.blockLength K : ℕ) : ℝ) ^ (-s.re))))
      atTop
      (nhds
        (|s.im| * ‖s‖ / s.re *
          (2 / (1 + 2 * S.density)) ^ s.re)) := by
  have hratio := S.leftEndpoint_over_blockStartIndex_tendsto
  have hratioPow := hratio.rpow_const
    (p := s.re)
    (Or.inl (by
      have ha : 0 < 1 + 2 * S.density := by linarith [S.density_pos]
      have : 0 < 2 / (1 + 2 * S.density) := div_pos (by norm_num) ha
      exact this.ne'))
  have hbase :
      Tendsto
        (fun K : ℕ =>
          |s.im| * ‖s‖ / s.re *
            (etaPairFrameLeftEndpoint K /
              ((K + S.blockLength K : ℕ) : ℝ)) ^ s.re)
        atTop
        (nhds
          (|s.im| * ‖s‖ / s.re *
            (2 / (1 + 2 * S.density)) ^ s.re)) := by
    simpa [mul_assoc] using
      (tendsto_const_nhds.mul hratioPow)
  refine hbase.congr' ?_
  filter_upwards [S.eventually_blockLength_pos] with K hN
  have hE : 0 < etaPairFrameLeftEndpoint K :=
    etaPairFrameLeftEndpoint_pos K
  have hL : 0 < ((K + S.blockLength K : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < K + S.blockLength K)
  rw [Real.div_rpow hE.le hL.le, Real.rpow_neg hL.le]
  field_simp [hE.ne', hL.ne']

/-!
The final two theorems compare the source objects themselves.  The residual
side is used only through its explicit power majorant, while the margin side
is the existing endpoint-power lower bound.  The dominant summand and the
margin limit are separated by a midpoint around the ZDI-009 strict constant
inequality.
-/

/--
The right positive-density source objects satisfy the normalized sixteen-fold
obstruction eventually.  The residual object in the conclusion is the
existing `etaCriticalMirrorBlockStartResidualTailPowerBound`, not a proxy
constant.
-/
theorem eventually_sixteen_mul_rightNormalizedBlockMarginPowerLowerBound_lt_residualPowerBound
    (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ}
    (hre : (1 : ℝ) / 2 < s.re)
    (hre1 : s.re < 1)
    (him : s.im ≠ 0) :
    ∀ᶠ K : ℕ in atTop,
      16 *
          (etaPairFrameLeftEndpoint K ^ (1 - s.re) *
            etaCriticalMirrorRightBlockMarginPowerLowerBound
              s K (S.blockLength K)) <
        etaPairFrameLeftEndpoint K ^ (1 - s.re) *
          etaCriticalMirrorBlockStartResidualTailPowerBound
            s K (S.blockLength K) := by
  have hconst :=
    right_normalizedResidualConstant_gt_sixteen_mul_marginConstant_of_point
      hre hre1 him S.density_pos
  have hmargin :
      Tendsto
        (fun K : ℕ =>
          etaPairFrameLeftEndpoint K ^ (1 - s.re) *
            etaCriticalMirrorRightBlockMarginPowerLowerBound
              s K (S.blockLength K))
        atTop
        (nhds
          (((s.im : ℝ) ^ 2 / 4) * S.density *
            (1 + 2 * S.density) ^ (s.re - 2))) := by
    simpa [mul_assoc] using
      S.rightNormalizedBlockMarginPowerLowerBound_tendsto s
  have hdominant := S.right_normalizedDominantResidualPower_tendsto hre hre1
  let marginConstant : ℝ :=
    ((s.im : ℝ) ^ 2 / 4) * S.density *
      (1 + 2 * S.density) ^ (s.re - 2)
  let residualConstant : ℝ :=
    |s.im| * ‖criticalMirror s‖ / (1 - s.re) *
      (2 / (1 + 2 * S.density)) ^ (1 - s.re)
  have hstrict : 16 * marginConstant < residualConstant := by
    simpa [marginConstant, residualConstant, mul_assoc] using hconst
  let midpoint : ℝ := (16 * marginConstant + residualConstant) / 2
  have hmargin_mid : 16 * marginConstant < midpoint := by
    dsimp [midpoint]
    linarith
  have hmid_residual : midpoint < residualConstant := by
    dsimp [midpoint]
    linarith
  have hmargin16 :
      Tendsto
        (fun K : ℕ =>
          16 *
            (etaPairFrameLeftEndpoint K ^ (1 - s.re) *
              etaCriticalMirrorRightBlockMarginPowerLowerBound
                s K (S.blockLength K)))
        atTop (nhds (16 * marginConstant)) := by
    simpa [marginConstant, mul_assoc] using
      (tendsto_const_nhds.mul hmargin)
  have hmargin_eventually :
      ∀ᶠ K : ℕ in atTop,
        16 *
            (etaPairFrameLeftEndpoint K ^ (1 - s.re) *
              etaCriticalMirrorRightBlockMarginPowerLowerBound
                s K (S.blockLength K)) < midpoint :=
    (tendsto_order.1 hmargin16).2 midpoint hmargin_mid
  have hdominant_eventually :
      ∀ᶠ K : ℕ in atTop,
        midpoint <
          etaPairFrameLeftEndpoint K ^ (1 - s.re) *
            (|s.im| * ‖criticalMirror s‖ / (1 - s.re) *
              (((K + S.blockLength K : ℕ) : ℝ) ^ (-(1 - s.re)))) :=
    (tendsto_order.1 hdominant).1 midpoint hmid_residual
  have hmajorant_eventually :
      ∀ᶠ K : ℕ in atTop,
        etaPairFrameLeftEndpoint K ^ (1 - s.re) *
            (|s.im| * ‖criticalMirror s‖ / (1 - s.re) *
              (((K + S.blockLength K : ℕ) : ℝ) ^ (-(1 - s.re)))) ≤
          etaPairFrameLeftEndpoint K ^ (1 - s.re) *
            etaCriticalMirrorBlockStartResidualTailPowerBound
              s K (S.blockLength K) := by
    filter_upwards [S.eventually_blockLength_pos] with K hN
    have hE : 0 < etaPairFrameLeftEndpoint K :=
      etaPairFrameLeftEndpoint_pos K
    have hL : 0 < ((K + S.blockLength K : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < K + S.blockLength K)
    have hden : 0 < 1 - s.re := by linarith
    have hraw :
        |s.im| * ‖criticalMirror s‖ / (1 - s.re) *
            (((K + S.blockLength K : ℕ) : ℝ) ^ (-(1 - s.re))) ≤
          etaCriticalMirrorBlockStartResidualTailPowerBound
            s K (S.blockLength K) := by
      unfold etaCriticalMirrorBlockStartResidualTailPowerBound
      unfold etaCriticalMirrorDefectPairTailPowerBound
      simp only [criticalMirror_re]
      calc
        |s.im| * ‖criticalMirror s‖ / (1 - s.re) *
              (((K + S.blockLength K : ℕ) : ℝ) ^ (-(1 - s.re))) =
            |s.im| *
              (‖criticalMirror s‖ *
                ((((K + S.blockLength K : ℕ) : ℝ) ^ (-(1 - s.re))) /
                  (1 - s.re))) := by ring
        _ ≤ |s.im| *
              (‖criticalMirror s‖ *
                ((((K + S.blockLength K : ℕ) : ℝ) ^ (-(1 - s.re))) /
                  (1 - s.re)) +
                ‖s‖ * ((((K + S.blockLength K : ℕ) : ℝ) ^ (-s.re)) / s.re)) := by
          have hnonneg :
              0 ≤ ‖s‖ *
                ((((K + S.blockLength K : ℕ) : ℝ) ^ (-s.re)) / s.re) := by
            positivity
          exact mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_right hnonneg) (abs_nonneg s.im)
    exact mul_le_mul_of_nonneg_left hraw
      (Real.rpow_pos_of_pos hE (1 - s.re)).le
  filter_upwards [hmargin_eventually, hdominant_eventually,
    hmajorant_eventually] with K hmarginK hdominantK hmajorantK
  exact (hmarginK.trans hdominantK).trans_le hmajorantK

/--
The left positive-density source objects satisfy the normalized sixteen-fold
obstruction eventually, with the original-side residual summand dominant.
-/
theorem eventually_sixteen_mul_leftNormalizedBlockMarginPowerLowerBound_lt_residualPowerBound
    (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ}
    (hre0 : 0 < s.re)
    (hre : s.re < (1 : ℝ) / 2)
    (him : s.im ≠ 0) :
    ∀ᶠ K : ℕ in atTop,
      16 *
          (etaPairFrameLeftEndpoint K ^ s.re *
            etaCriticalMirrorLeftBlockMarginPowerLowerBound
              s K (S.blockLength K)) <
        etaPairFrameLeftEndpoint K ^ s.re *
          etaCriticalMirrorBlockStartResidualTailPowerBound
            s K (S.blockLength K) := by
  have hconst :=
    left_normalizedResidualConstant_gt_sixteen_mul_marginConstant_of_point
      hre0 hre him S.density_pos
  have hmargin :
      Tendsto
        (fun K : ℕ =>
          etaPairFrameLeftEndpoint K ^ s.re *
            etaCriticalMirrorLeftBlockMarginPowerLowerBound
              s K (S.blockLength K))
        atTop
        (nhds
          (((s.im : ℝ) ^ 2 / 4) * S.density *
            (1 + 2 * S.density) ^ (-s.re - 1))) := by
    simpa [mul_assoc] using
      S.leftNormalizedBlockMarginPowerLowerBound_tendsto s
  have hdominant := S.left_normalizedDominantResidualPower_tendsto hre0 hre
  let marginConstant : ℝ :=
    ((s.im : ℝ) ^ 2 / 4) * S.density *
      (1 + 2 * S.density) ^ (-s.re - 1)
  let residualConstant : ℝ :=
    |s.im| * ‖s‖ / s.re *
      (2 / (1 + 2 * S.density)) ^ s.re
  have hstrict : 16 * marginConstant < residualConstant := by
    simpa [marginConstant, residualConstant, mul_assoc] using hconst
  let midpoint : ℝ := (16 * marginConstant + residualConstant) / 2
  have hmargin_mid : 16 * marginConstant < midpoint := by
    dsimp [midpoint]
    linarith
  have hmid_residual : midpoint < residualConstant := by
    dsimp [midpoint]
    linarith
  have hmargin16 :
      Tendsto
        (fun K : ℕ =>
          16 *
            (etaPairFrameLeftEndpoint K ^ s.re *
              etaCriticalMirrorLeftBlockMarginPowerLowerBound
                s K (S.blockLength K)))
        atTop (nhds (16 * marginConstant)) := by
    simpa [marginConstant, mul_assoc] using
      (tendsto_const_nhds.mul hmargin)
  have hmargin_eventually :
      ∀ᶠ K : ℕ in atTop,
        16 *
            (etaPairFrameLeftEndpoint K ^ s.re *
              etaCriticalMirrorLeftBlockMarginPowerLowerBound
                s K (S.blockLength K)) < midpoint :=
    (tendsto_order.1 hmargin16).2 midpoint hmargin_mid
  have hdominant_eventually :
      ∀ᶠ K : ℕ in atTop,
        midpoint <
          etaPairFrameLeftEndpoint K ^ s.re *
            (|s.im| * ‖s‖ / s.re *
              (((K + S.blockLength K : ℕ) : ℝ) ^ (-s.re))) :=
    (tendsto_order.1 hdominant).1 midpoint hmid_residual
  have hmajorant_eventually :
      ∀ᶠ K : ℕ in atTop,
        etaPairFrameLeftEndpoint K ^ s.re *
            (|s.im| * ‖s‖ / s.re *
              (((K + S.blockLength K : ℕ) : ℝ) ^ (-s.re))) ≤
          etaPairFrameLeftEndpoint K ^ s.re *
            etaCriticalMirrorBlockStartResidualTailPowerBound
              s K (S.blockLength K) := by
    filter_upwards [S.eventually_blockLength_pos] with K hN
    have hE : 0 < etaPairFrameLeftEndpoint K :=
      etaPairFrameLeftEndpoint_pos K
    have hL : 0 < ((K + S.blockLength K : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < K + S.blockLength K)
    have hden : 0 < s.re := hre0
    have hmirrorden : 0 < 1 - s.re := by linarith
    have hraw :
        |s.im| * ‖s‖ / s.re *
            (((K + S.blockLength K : ℕ) : ℝ) ^ (-s.re)) ≤
          etaCriticalMirrorBlockStartResidualTailPowerBound
            s K (S.blockLength K) := by
      unfold etaCriticalMirrorBlockStartResidualTailPowerBound
      unfold etaCriticalMirrorDefectPairTailPowerBound
      simp only [criticalMirror_re]
      calc
        |s.im| * ‖s‖ / s.re *
              (((K + S.blockLength K : ℕ) : ℝ) ^ (-s.re)) =
            |s.im| *
              (‖s‖ *
                ((((K + S.blockLength K : ℕ) : ℝ) ^ (-s.re)) / s.re)) := by ring
        _ ≤ |s.im| *
              (‖criticalMirror s‖ *
                ((((K + S.blockLength K : ℕ) : ℝ) ^ (-(1 - s.re))) /
                  (1 - s.re)) +
                ‖s‖ * ((((K + S.blockLength K : ℕ) : ℝ) ^ (-s.re)) / s.re)) := by
          have hnonneg :
              0 ≤ ‖criticalMirror s‖ *
                ((((K + S.blockLength K : ℕ) : ℝ) ^ (-(1 - s.re))) /
                  (1 - s.re)) := by
            positivity
          exact mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_left hnonneg) (abs_nonneg s.im)
    exact mul_le_mul_of_nonneg_left hraw
      (Real.rpow_pos_of_pos hE s.re).le
  filter_upwards [hmargin_eventually, hdominant_eventually,
    hmajorant_eventually] with K hmarginK hdominantK hmajorantK
  exact (hmarginK.trans hdominantK).trans_le hmajorantK

end EtaPairPositiveDensityBlockSchedule

end DkMath.RH.CFBRCProjection
