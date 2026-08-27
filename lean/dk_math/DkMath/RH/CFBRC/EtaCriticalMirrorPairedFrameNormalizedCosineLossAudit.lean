/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCosineLossBound
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedCorrectionEndpointAudit
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedCosineLossAudit"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-- Mirror-side constant in the explicit cosine-loss tail power bound. -/
noncomputable def etaCriticalMirrorCosineLossMirrorTailConstant
    (s : ℂ) : ℝ :=
  (2 * |s.im| ^ 3 * ‖criticalMirror s‖ /
      (criticalMirror s).re) /
    ((criticalMirror s).re + 1)

/-- Original-side constant in the explicit cosine-loss tail power bound. -/
noncomputable def etaCriticalMirrorCosineLossOriginalTailConstant
    (s : ℂ) : ℝ :=
  (2 * |s.im| ^ 3 * ‖s‖ / s.re) /
    (s.re + 1)

/-- The cosine-loss tail power bound is exactly the sum of its two named powers. -/
theorem etaCriticalMirrorPairedFrameCorrectionCosineLossTailPowerBound_eq_constants
    (s : ℂ) (K : ℕ) :
    etaCriticalMirrorPairedFrameCorrectionCosineLossTailPowerBound s K =
      etaCriticalMirrorCosineLossMirrorTailConstant s *
          ((K : ℝ) ^ (-(criticalMirror s).re - 1)) +
        etaCriticalMirrorCosineLossOriginalTailConstant s *
          ((K : ℝ) ^ (-s.re - 1)) := by
  unfold etaCriticalMirrorPairedFrameCorrectionCosineLossTailPowerBound
  unfold etaCriticalMirrorCosineLossMirrorTailConstant
  unfold etaCriticalMirrorCosineLossOriginalTailConstant
  ring

/-- Right-side `K`-normalized cosine-loss audit. -/
noncomputable def etaCriticalMirrorRightIndexNormalizedCosineLossPowerAudit
    (s : ℂ) (K : ℕ) : ℝ :=
  etaCriticalMirrorCosineLossMirrorTailConstant s *
      ((K : ℝ) ^ (-1 : ℝ)) +
    etaCriticalMirrorCosineLossOriginalTailConstant s *
      ((K : ℝ) ^ (-(s.re - (criticalMirror s).re + 1)))

/-- Left-side `K`-normalized cosine-loss audit. -/
noncomputable def etaCriticalMirrorLeftIndexNormalizedCosineLossPowerAudit
    (s : ℂ) (K : ℕ) : ℝ :=
  etaCriticalMirrorCosineLossMirrorTailConstant s *
      ((K : ℝ) ^ (-((criticalMirror s).re - s.re + 1))) +
    etaCriticalMirrorCosineLossOriginalTailConstant s *
      ((K : ℝ) ^ (-1 : ℝ))

/-- Eventually, right normalization of the power bound is exactly the right audit. -/
theorem eventually_etaCriticalMirrorRightIndexNormalizedCosineLossPowerBound_eq_audit
    (s : ℂ) :
    ∀ᶠ K : ℕ in atTop,
      ((K : ℝ) ^ (criticalMirror s).re) *
          etaCriticalMirrorPairedFrameCorrectionCosineLossTailPowerBound s K =
        etaCriticalMirrorRightIndexNormalizedCosineLossPowerAudit s K := by
  filter_upwards [eventually_ge_atTop 1] with K hK
  have hKpos : 0 < (K : ℝ) := by
    exact_mod_cast hK
  have hmirror :
      ((K : ℝ) ^ (criticalMirror s).re) *
          ((K : ℝ) ^ (-(criticalMirror s).re - 1)) =
        (K : ℝ) ^ (-1 : ℝ) := by
    calc
      ((K : ℝ) ^ (criticalMirror s).re) *
          ((K : ℝ) ^ (-(criticalMirror s).re - 1)) =
        (K : ℝ) ^
          ((criticalMirror s).re + (-(criticalMirror s).re - 1)) :=
            (Real.rpow_add hKpos _ _).symm
      _ = (K : ℝ) ^ (-1 : ℝ) := by
        congr 1
        ring
  have horiginal :
      ((K : ℝ) ^ (criticalMirror s).re) *
          ((K : ℝ) ^ (-s.re - 1)) =
        (K : ℝ) ^ (-(s.re - (criticalMirror s).re + 1)) := by
    calc
      ((K : ℝ) ^ (criticalMirror s).re) *
          ((K : ℝ) ^ (-s.re - 1)) =
        (K : ℝ) ^ ((criticalMirror s).re + (-s.re - 1)) :=
          (Real.rpow_add hKpos _ _).symm
      _ = (K : ℝ) ^ (-(s.re - (criticalMirror s).re + 1)) := by
        congr 1
        ring
  rw [etaCriticalMirrorPairedFrameCorrectionCosineLossTailPowerBound_eq_constants]
  unfold etaCriticalMirrorRightIndexNormalizedCosineLossPowerAudit
  calc
    ((K : ℝ) ^ (criticalMirror s).re) *
        (etaCriticalMirrorCosineLossMirrorTailConstant s *
            ((K : ℝ) ^ (-(criticalMirror s).re - 1)) +
          etaCriticalMirrorCosineLossOriginalTailConstant s *
            ((K : ℝ) ^ (-s.re - 1))) =
      etaCriticalMirrorCosineLossMirrorTailConstant s *
          (((K : ℝ) ^ (criticalMirror s).re) *
            ((K : ℝ) ^ (-(criticalMirror s).re - 1))) +
        etaCriticalMirrorCosineLossOriginalTailConstant s *
          (((K : ℝ) ^ (criticalMirror s).re) *
            ((K : ℝ) ^ (-s.re - 1))) := by ring
    _ = etaCriticalMirrorCosineLossMirrorTailConstant s *
          ((K : ℝ) ^ (-1 : ℝ)) +
        etaCriticalMirrorCosineLossOriginalTailConstant s *
          ((K : ℝ) ^ (-(s.re - (criticalMirror s).re + 1))) := by
      rw [hmirror, horiginal]

/-- Eventually, left normalization of the power bound is exactly the left audit. -/
theorem eventually_etaCriticalMirrorLeftIndexNormalizedCosineLossPowerBound_eq_audit
    (s : ℂ) :
    ∀ᶠ K : ℕ in atTop,
      ((K : ℝ) ^ s.re) *
          etaCriticalMirrorPairedFrameCorrectionCosineLossTailPowerBound s K =
        etaCriticalMirrorLeftIndexNormalizedCosineLossPowerAudit s K := by
  filter_upwards [eventually_ge_atTop 1] with K hK
  have hKpos : 0 < (K : ℝ) := by
    exact_mod_cast hK
  have hmirror :
      ((K : ℝ) ^ s.re) *
          ((K : ℝ) ^ (-(criticalMirror s).re - 1)) =
        (K : ℝ) ^ (-((criticalMirror s).re - s.re + 1)) := by
    calc
      ((K : ℝ) ^ s.re) *
          ((K : ℝ) ^ (-(criticalMirror s).re - 1)) =
        (K : ℝ) ^ (s.re + (-(criticalMirror s).re - 1)) :=
          (Real.rpow_add hKpos _ _).symm
      _ = (K : ℝ) ^ (-((criticalMirror s).re - s.re + 1)) := by
        congr 1
        ring
  have horiginal :
      ((K : ℝ) ^ s.re) * ((K : ℝ) ^ (-s.re - 1)) =
        (K : ℝ) ^ (-1 : ℝ) := by
    calc
      ((K : ℝ) ^ s.re) * ((K : ℝ) ^ (-s.re - 1)) =
        (K : ℝ) ^ (s.re + (-s.re - 1)) :=
          (Real.rpow_add hKpos _ _).symm
      _ = (K : ℝ) ^ (-1 : ℝ) := by
        congr 1
        ring
  rw [etaCriticalMirrorPairedFrameCorrectionCosineLossTailPowerBound_eq_constants]
  unfold etaCriticalMirrorLeftIndexNormalizedCosineLossPowerAudit
  calc
    ((K : ℝ) ^ s.re) *
        (etaCriticalMirrorCosineLossMirrorTailConstant s *
            ((K : ℝ) ^ (-(criticalMirror s).re - 1)) +
          etaCriticalMirrorCosineLossOriginalTailConstant s *
            ((K : ℝ) ^ (-s.re - 1))) =
      etaCriticalMirrorCosineLossMirrorTailConstant s *
          (((K : ℝ) ^ s.re) *
            ((K : ℝ) ^ (-(criticalMirror s).re - 1))) +
        etaCriticalMirrorCosineLossOriginalTailConstant s *
          (((K : ℝ) ^ s.re) * ((K : ℝ) ^ (-s.re - 1))) := by ring
    _ = etaCriticalMirrorCosineLossMirrorTailConstant s *
          ((K : ℝ) ^ (-((criticalMirror s).re - s.re + 1))) +
        etaCriticalMirrorCosineLossOriginalTailConstant s *
          ((K : ℝ) ^ (-1 : ℝ)) := by
      rw [hmirror, horiginal]

/-- The right `K`-normalized cosine-loss power audit tends to zero. -/
theorem etaCriticalMirrorRightIndexNormalizedCosineLossPowerAudit_tendsto_zero
    {s : ℂ} (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (etaCriticalMirrorRightIndexNormalizedCosineLossPowerAudit s)
      atTop (nhds 0) := by
  have hcrossPos :
      0 < s.re - (criticalMirror s).re + 1 := by
    rw [criticalMirror_re]
    linarith
  have hone :
      Tendsto (fun K : ℕ => ((K : ℝ) ^ (-1 : ℝ)))
        atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop zero_lt_one).comp
      tendsto_natCast_atTop_atTop
  have hcross :
      Tendsto
        (fun K : ℕ =>
          ((K : ℝ) ^ (-(s.re - (criticalMirror s).re + 1))))
        atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hcrossPos).comp
      tendsto_natCast_atTop_atTop
  change Tendsto
    (fun K : ℕ =>
      etaCriticalMirrorCosineLossMirrorTailConstant s *
          ((K : ℝ) ^ (-1 : ℝ)) +
        etaCriticalMirrorCosineLossOriginalTailConstant s *
          ((K : ℝ) ^ (-(s.re - (criticalMirror s).re + 1))))
    atTop _
  simpa using
    (tendsto_const_nhds.mul hone).add
      (tendsto_const_nhds.mul hcross)

/-- The left `K`-normalized cosine-loss power audit tends to zero. -/
theorem etaCriticalMirrorLeftIndexNormalizedCosineLossPowerAudit_tendsto_zero
    {s : ℂ} (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (etaCriticalMirrorLeftIndexNormalizedCosineLossPowerAudit s)
      atTop (nhds 0) := by
  have hcrossPos :
      0 < (criticalMirror s).re - s.re + 1 := by
    rw [criticalMirror_re]
    linarith
  have hone :
      Tendsto (fun K : ℕ => ((K : ℝ) ^ (-1 : ℝ)))
        atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop zero_lt_one).comp
      tendsto_natCast_atTop_atTop
  have hcross :
      Tendsto
        (fun K : ℕ =>
          ((K : ℝ) ^ (-((criticalMirror s).re - s.re + 1))))
        atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hcrossPos).comp
      tendsto_natCast_atTop_atTop
  change Tendsto
    (fun K : ℕ =>
      etaCriticalMirrorCosineLossMirrorTailConstant s *
          ((K : ℝ) ^ (-((criticalMirror s).re - s.re + 1))) +
        etaCriticalMirrorCosineLossOriginalTailConstant s *
          ((K : ℝ) ^ (-1 : ℝ)))
    atTop _
  simpa using
    (tendsto_const_nhds.mul hcross).add
      (tendsto_const_nhds.mul hone)

/-- The right `K`-normalized cosine-loss power bound tends to zero. -/
theorem etaCriticalMirrorRightIndexNormalizedCosineLossPowerBound_tendsto_zero
    {s : ℂ} (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (fun K : ℕ =>
        ((K : ℝ) ^ (criticalMirror s).re) *
          etaCriticalMirrorPairedFrameCorrectionCosineLossTailPowerBound s K)
      atTop (nhds 0) := by
  refine
    (etaCriticalMirrorRightIndexNormalizedCosineLossPowerAudit_tendsto_zero hre).congr' ?_
  exact
    (eventually_etaCriticalMirrorRightIndexNormalizedCosineLossPowerBound_eq_audit s).mono
      (fun _ h => h.symm)

/-- The left `K`-normalized cosine-loss power bound tends to zero. -/
theorem etaCriticalMirrorLeftIndexNormalizedCosineLossPowerBound_tendsto_zero
    {s : ℂ} (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (fun K : ℕ =>
        ((K : ℝ) ^ s.re) *
          etaCriticalMirrorPairedFrameCorrectionCosineLossTailPowerBound s K)
      atTop (nhds 0) := by
  refine
    (etaCriticalMirrorLeftIndexNormalizedCosineLossPowerAudit_tendsto_zero hre).congr' ?_
  exact
    (eventually_etaCriticalMirrorLeftIndexNormalizedCosineLossPowerBound_eq_audit s).mono
      (fun _ h => h.symm)

/-- The actual right `K`-normalized cosine-loss tail tends to zero. -/
theorem etaCriticalMirrorRightIndexNormalizedCosineLossTail_tendsto_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (fun K : ℕ =>
        ((K : ℝ) ^ (criticalMirror s).re) *
          etaCriticalMirrorPairedFrameCorrectionCosineLossTail K s)
      atTop (nhds 0) := by
  have hupper :=
    etaCriticalMirrorRightIndexNormalizedCosineLossPowerBound_tendsto_zero hre
  have hlower :
      Tendsto
        (fun K : ℕ =>
          -(((K : ℝ) ^ (criticalMirror s).re) *
            etaCriticalMirrorPairedFrameCorrectionCosineLossTailPowerBound s K))
        atTop (nhds 0) := by
    simpa using hupper.neg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [eventually_ge_atTop 1] with K hK
    have hKpos : 0 < (K : ℝ) := by
      exact_mod_cast hK
    have hscaleNonneg : 0 ≤ (K : ℝ) ^ (criticalMirror s).re :=
      (Real.rpow_pos_of_pos hKpos _).le
    have htail :=
      abs_etaCriticalMirrorPairedFrameCorrectionCosineLossTail_le_powerBound
        hs him hK
    have habs :
        |((K : ℝ) ^ (criticalMirror s).re) *
            etaCriticalMirrorPairedFrameCorrectionCosineLossTail K s| ≤
          ((K : ℝ) ^ (criticalMirror s).re) *
            etaCriticalMirrorPairedFrameCorrectionCosineLossTailPowerBound s K := by
      rw [abs_mul, abs_of_nonneg hscaleNonneg]
      exact mul_le_mul_of_nonneg_left htail hscaleNonneg
    exact (abs_le.mp habs).1
  · filter_upwards [eventually_ge_atTop 1] with K hK
    have hKpos : 0 < (K : ℝ) := by
      exact_mod_cast hK
    have hscaleNonneg : 0 ≤ (K : ℝ) ^ (criticalMirror s).re :=
      (Real.rpow_pos_of_pos hKpos _).le
    have htail :=
      abs_etaCriticalMirrorPairedFrameCorrectionCosineLossTail_le_powerBound
        hs him hK
    have habs :
        |((K : ℝ) ^ (criticalMirror s).re) *
            etaCriticalMirrorPairedFrameCorrectionCosineLossTail K s| ≤
          ((K : ℝ) ^ (criticalMirror s).re) *
            etaCriticalMirrorPairedFrameCorrectionCosineLossTailPowerBound s K := by
      rw [abs_mul, abs_of_nonneg hscaleNonneg]
      exact mul_le_mul_of_nonneg_left htail hscaleNonneg
    exact (abs_le.mp habs).2

/-- The actual left `K`-normalized cosine-loss tail tends to zero. -/
theorem etaCriticalMirrorLeftIndexNormalizedCosineLossTail_tendsto_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (fun K : ℕ =>
        ((K : ℝ) ^ s.re) *
          etaCriticalMirrorPairedFrameCorrectionCosineLossTail K s)
      atTop (nhds 0) := by
  have hupper :=
    etaCriticalMirrorLeftIndexNormalizedCosineLossPowerBound_tendsto_zero hre
  have hlower :
      Tendsto
        (fun K : ℕ =>
          -(((K : ℝ) ^ s.re) *
            etaCriticalMirrorPairedFrameCorrectionCosineLossTailPowerBound s K))
        atTop (nhds 0) := by
    simpa using hupper.neg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [eventually_ge_atTop 1] with K hK
    have hKpos : 0 < (K : ℝ) := by
      exact_mod_cast hK
    have hscaleNonneg : 0 ≤ (K : ℝ) ^ s.re :=
      (Real.rpow_pos_of_pos hKpos _).le
    have htail :=
      abs_etaCriticalMirrorPairedFrameCorrectionCosineLossTail_le_powerBound
        hs him hK
    have habs :
        |((K : ℝ) ^ s.re) *
            etaCriticalMirrorPairedFrameCorrectionCosineLossTail K s| ≤
          ((K : ℝ) ^ s.re) *
            etaCriticalMirrorPairedFrameCorrectionCosineLossTailPowerBound s K := by
      rw [abs_mul, abs_of_nonneg hscaleNonneg]
      exact mul_le_mul_of_nonneg_left htail hscaleNonneg
    exact (abs_le.mp habs).1
  · filter_upwards [eventually_ge_atTop 1] with K hK
    have hKpos : 0 < (K : ℝ) := by
      exact_mod_cast hK
    have hscaleNonneg : 0 ≤ (K : ℝ) ^ s.re :=
      (Real.rpow_pos_of_pos hKpos _).le
    have htail :=
      abs_etaCriticalMirrorPairedFrameCorrectionCosineLossTail_le_powerBound
        hs him hK
    have habs :
        |((K : ℝ) ^ s.re) *
            etaCriticalMirrorPairedFrameCorrectionCosineLossTail K s| ≤
          ((K : ℝ) ^ s.re) *
            etaCriticalMirrorPairedFrameCorrectionCosineLossTailPowerBound s K := by
      rw [abs_mul, abs_of_nonneg hscaleNonneg]
      exact mul_le_mul_of_nonneg_left htail hscaleNonneg
    exact (abs_le.mp habs).2

/-- Shifted pair-left normalization of the right cosine-loss tail tends to zero. -/
theorem etaCriticalMirrorRightShiftedLeftEndpointNormalizedCosineLossTail_tendsto_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (fun K : ℕ =>
        etaPairFrameLeftEndpoint (K + 1) ^ (criticalMirror s).re *
          etaCriticalMirrorPairedFrameCorrectionCosineLossTail K s)
      atTop (nhds 0) := by
  have hratio :=
    etaPairFrameLeftEndpoint_succ_div_index_rpow_tendsto
      (criticalMirror s).re
  have hindex :=
    etaCriticalMirrorRightIndexNormalizedCosineLossTail_tendsto_zero
      hs him hre
  have hprod :
      Tendsto
        (fun K : ℕ =>
          (etaPairFrameLeftEndpoint (K + 1) / (K : ℝ)) ^
              (criticalMirror s).re *
            (((K : ℝ) ^ (criticalMirror s).re) *
              etaCriticalMirrorPairedFrameCorrectionCosineLossTail K s))
        atTop (nhds 0) := by
    simpa using hratio.mul hindex
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with K hK
  have hKpos : 0 < (K : ℝ) := by
    exact_mod_cast hK
  have hKpow : (K : ℝ) ^ (criticalMirror s).re ≠ 0 :=
    (Real.rpow_pos_of_pos hKpos _).ne'
  rw [Real.div_rpow
    (etaPairFrameLeftEndpoint_pos (K + 1)).le hKpos.le]
  field_simp [hKpow]

/-- Shifted pair-left normalization of the left cosine-loss tail tends to zero. -/
theorem etaCriticalMirrorLeftShiftedLeftEndpointNormalizedCosineLossTail_tendsto_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (fun K : ℕ =>
        etaPairFrameLeftEndpoint (K + 1) ^ s.re *
          etaCriticalMirrorPairedFrameCorrectionCosineLossTail K s)
      atTop (nhds 0) := by
  have hratio :=
    etaPairFrameLeftEndpoint_succ_div_index_rpow_tendsto s.re
  have hindex :=
    etaCriticalMirrorLeftIndexNormalizedCosineLossTail_tendsto_zero
      hs him hre
  have hprod :
      Tendsto
        (fun K : ℕ =>
          (etaPairFrameLeftEndpoint (K + 1) / (K : ℝ)) ^ s.re *
            (((K : ℝ) ^ s.re) *
              etaCriticalMirrorPairedFrameCorrectionCosineLossTail K s))
        atTop (nhds 0) := by
    simpa using hratio.mul hindex
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with K hK
  have hKpos : 0 < (K : ℝ) := by
    exact_mod_cast hK
  have hKpow : (K : ℝ) ^ s.re ≠ 0 :=
    (Real.rpow_pos_of_pos hKpos _).ne'
  rw [Real.div_rpow
    (etaPairFrameLeftEndpoint_pos (K + 1)).le hKpos.le]
  field_simp [hKpow]

/-- Current-endpoint normalization of the predecessor right cosine-loss tail tends to zero. -/
theorem etaCriticalMirrorRightPredecessorLeftEndpointNormalizedCosineLossTail_tendsto_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (fun K : ℕ =>
        etaPairFrameLeftEndpoint K ^ (criticalMirror s).re *
          etaCriticalMirrorPairedFrameCorrectionCosineLossTail (K - 1) s)
      atTop (nhds 0) := by
  have hshift :=
    etaCriticalMirrorRightShiftedLeftEndpointNormalizedCosineLossTail_tendsto_zero
      hs him hre
  have hpred :
      Tendsto
        (fun K : ℕ =>
          etaPairFrameLeftEndpoint (Nat.pred K + 1) ^
              (criticalMirror s).re *
            etaCriticalMirrorPairedFrameCorrectionCosineLossTail
              (Nat.pred K) s)
        atTop (nhds 0) := by
    simpa only [Function.comp_apply, Function.comp_def, Nat.pred_eq_sub_one] using
      hshift.comp tendsto_nat_pred_atTop
  refine hpred.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with K hK
  have hsucc : Nat.pred K + 1 = K := Nat.succ_pred_eq_of_pos hK
  have hpredEq : Nat.pred K = K - 1 := by
    simp only [Nat.pred_eq_sub_one]
  rw [hsucc, hpredEq]

/-- Current-endpoint normalization of the predecessor left cosine-loss tail tends to zero. -/
theorem etaCriticalMirrorLeftPredecessorLeftEndpointNormalizedCosineLossTail_tendsto_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (fun K : ℕ =>
        etaPairFrameLeftEndpoint K ^ s.re *
          etaCriticalMirrorPairedFrameCorrectionCosineLossTail (K - 1) s)
      atTop (nhds 0) := by
  have hshift :=
    etaCriticalMirrorLeftShiftedLeftEndpointNormalizedCosineLossTail_tendsto_zero
      hs him hre
  have hpred :
      Tendsto
        (fun K : ℕ =>
          etaPairFrameLeftEndpoint (Nat.pred K + 1) ^ s.re *
            etaCriticalMirrorPairedFrameCorrectionCosineLossTail
              (Nat.pred K) s)
        atTop (nhds 0) := by
    simpa only [Function.comp_apply, Function.comp_def, Nat.pred_eq_sub_one] using
      hshift.comp tendsto_nat_pred_atTop
  refine hpred.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with K hK
  have hsucc : Nat.pred K + 1 = K := Nat.succ_pred_eq_of_pos hK
  have hpredEq : Nat.pred K = K - 1 := by
    simp only [Nat.pred_eq_sub_one]
  rw [hsucc, hpredEq]

end DkMath.RH.CFBRCProjection
