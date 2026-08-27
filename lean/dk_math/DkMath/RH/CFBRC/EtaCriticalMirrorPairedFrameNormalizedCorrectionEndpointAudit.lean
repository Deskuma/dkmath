/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedCorrectionAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedCorrectionEndpointAudit"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-- Right correction constant after transferring the index scale to the pair-left endpoint scale. -/
noncomputable def etaCriticalMirrorRightLeftEndpointNormalizedCorrectionConstant
    (s : ℂ) : ℝ :=
  (2 : ℝ) ^ (criticalMirror s).re *
    etaCriticalMirrorCorrectionMirrorProjectionConstant s

/-- Left correction constant after transferring the index scale to the pair-left endpoint scale. -/
noncomputable def etaCriticalMirrorLeftLeftEndpointNormalizedCorrectionConstant
    (s : ℂ) : ℝ :=
  (2 : ℝ) ^ s.re *
    etaCriticalMirrorCorrectionOriginalProjectionConstant s

/-- The shifted pair-left endpoint divided by the unshifted index tends to `2`. -/
theorem etaPairFrameLeftEndpoint_succ_div_index_tendsto_two :
    Tendsto
      (fun K : ℕ =>
        etaPairFrameLeftEndpoint (K + 1) / (K : ℝ))
      atTop (nhds 2) := by
  have hinv :
      Tendsto
        (fun K : ℕ => (3 : ℝ) / (K : ℝ))
        atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 3
  have hsum :
      Tendsto
        (fun K : ℕ => (2 : ℝ) + 3 / (K : ℝ))
        atTop (nhds ((2 : ℝ) + 0)) :=
    tendsto_const_nhds.add hinv
  have hsum' :
      Tendsto
        (fun K : ℕ => (2 : ℝ) + 3 / (K : ℝ))
        atTop (nhds 2) := by
    simpa using hsum
  refine hsum'.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with K hK
  have hKpos : 0 < (K : ℝ) := by
    exact_mod_cast hK
  unfold etaPairFrameLeftEndpoint
  norm_num [Nat.cast_add, Nat.cast_mul]
  field_simp [hKpos.ne']; ring

/-- Every fixed real power of the shifted endpoint/index ratio tends to the same power of `2`. -/
theorem etaPairFrameLeftEndpoint_succ_div_index_rpow_tendsto
    (q : ℝ) :
    Tendsto
      (fun K : ℕ =>
        (etaPairFrameLeftEndpoint (K + 1) / (K : ℝ)) ^ q)
      atTop (nhds ((2 : ℝ) ^ q)) := by
  exact
    etaPairFrameLeftEndpoint_succ_div_index_tendsto_two.rpow_const
      (Or.inl (by norm_num : (2 : ℝ) ≠ 0))

/--
On the right of the critical line, shifting the pair-left endpoint by one
transfers the index-normalized correction limit to the pair-left scale.
-/
theorem etaCriticalMirrorRightShiftedLeftEndpointNormalizedCorrectionPowerBound_tendsto
    {s : ℂ} (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (fun K : ℕ =>
        etaPairFrameLeftEndpoint (K + 1) ^ (criticalMirror s).re *
          etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound s K)
      atTop
      (nhds
        (etaCriticalMirrorRightLeftEndpointNormalizedCorrectionConstant s)) := by
  unfold etaCriticalMirrorRightLeftEndpointNormalizedCorrectionConstant
  have hratio :=
    etaPairFrameLeftEndpoint_succ_div_index_rpow_tendsto
      (criticalMirror s).re
  have hindex :=
    etaCriticalMirrorRightIndexNormalizedCorrectionPowerBound_tendsto hre
  refine (hratio.mul hindex).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with K hK
  have hKpos : 0 < (K : ℝ) := by
    exact_mod_cast hK
  have hKpow :
      (K : ℝ) ^ (criticalMirror s).re ≠ 0 :=
    (Real.rpow_pos_of_pos hKpos _).ne'
  rw [Real.div_rpow
    (etaPairFrameLeftEndpoint_pos (K + 1)).le hKpos.le]
  field_simp [hKpow]

/--
On the left of the critical line, shifting the pair-left endpoint by one
transfers the index-normalized correction limit to the pair-left scale.
-/
theorem etaCriticalMirrorLeftShiftedLeftEndpointNormalizedCorrectionPowerBound_tendsto
    {s : ℂ} (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (fun K : ℕ =>
        etaPairFrameLeftEndpoint (K + 1) ^ s.re *
          etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound s K)
      atTop
      (nhds
        (etaCriticalMirrorLeftLeftEndpointNormalizedCorrectionConstant s)) := by
  unfold etaCriticalMirrorLeftLeftEndpointNormalizedCorrectionConstant
  have hratio :=
    etaPairFrameLeftEndpoint_succ_div_index_rpow_tendsto s.re
  have hindex :=
    etaCriticalMirrorLeftIndexNormalizedCorrectionPowerBound_tendsto hre
  refine (hratio.mul hindex).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with K hK
  have hKpos : 0 < (K : ℝ) := by
    exact_mod_cast hK
  have hKpow :
      (K : ℝ) ^ s.re ≠ 0 :=
    (Real.rpow_pos_of_pos hKpos _).ne'
  rw [Real.div_rpow
    (etaPairFrameLeftEndpoint_pos (K + 1)).le hKpos.le]
  field_simp [hKpow]

/--
Right-side predecessor correction bound, normalized by the current pair-left
endpoint, tends to the right pair-left correction constant.
-/
theorem etaCriticalMirrorRightPredecessorLeftEndpointNormalizedCorrectionPowerBound_tendsto
    {s : ℂ} (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (fun K : ℕ =>
        etaPairFrameLeftEndpoint K ^ (criticalMirror s).re *
          etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound
            s (K - 1))
      atTop
      (nhds
        (etaCriticalMirrorRightLeftEndpointNormalizedCorrectionConstant s)) := by
  have hshift :=
    etaCriticalMirrorRightShiftedLeftEndpointNormalizedCorrectionPowerBound_tendsto
      hre
  have hpred :
      Tendsto
        (fun K : ℕ =>
          etaPairFrameLeftEndpoint (Nat.pred K + 1) ^
              (criticalMirror s).re *
            etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound
              s (Nat.pred K))
        atTop
        (nhds
          (etaCriticalMirrorRightLeftEndpointNormalizedCorrectionConstant s)) := by
    simpa only [Function.comp_apply, Function.comp_def, Nat.pred_eq_sub_one] using
      hshift.comp tendsto_nat_pred_atTop
  refine hpred.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with K hK
  have hsucc : Nat.pred K + 1 = K := Nat.succ_pred_eq_of_pos hK
  have hpredEq : Nat.pred K = K - 1 := by
    simp only [Nat.pred_eq_sub_one]
  rw [hsucc, hpredEq]

/--
Left-side predecessor correction bound, normalized by the current pair-left
endpoint, tends to the left pair-left correction constant.
-/
theorem etaCriticalMirrorLeftPredecessorLeftEndpointNormalizedCorrectionPowerBound_tendsto
    {s : ℂ} (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (fun K : ℕ =>
        etaPairFrameLeftEndpoint K ^ s.re *
          etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound
            s (K - 1))
      atTop
      (nhds
        (etaCriticalMirrorLeftLeftEndpointNormalizedCorrectionConstant s)) := by
  have hshift :=
    etaCriticalMirrorLeftShiftedLeftEndpointNormalizedCorrectionPowerBound_tendsto
      hre
  have hpred :
      Tendsto
        (fun K : ℕ =>
          etaPairFrameLeftEndpoint (Nat.pred K + 1) ^ s.re *
            etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound
              s (Nat.pred K))
        atTop
        (nhds
          (etaCriticalMirrorLeftLeftEndpointNormalizedCorrectionConstant s)) := by
    simpa only [Function.comp_apply, Function.comp_def, Nat.pred_eq_sub_one] using
      hshift.comp tendsto_nat_pred_atTop
  refine hpred.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with K hK
  have hsucc : Nat.pred K + 1 = K := Nat.succ_pred_eq_of_pos hK
  have hpredEq : Nat.pred K = K - 1 := by
    simp only [Nat.pred_eq_sub_one]
  rw [hsucc, hpredEq]

end DkMath.RH.CFBRCProjection
