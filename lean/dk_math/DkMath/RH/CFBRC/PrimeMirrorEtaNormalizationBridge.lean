/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PrimeMirrorEtaEnergyBridge
import DkMath.RH.CFBRC.EtaMirrorUnitSplit
import DkMath.RH.Weave.Analytic.EtaHalfPlaneReconstruction
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.PrimeMirrorEtaNormalizationBridge"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology
open DkMath.Algebra.MetallicRatioCore
open DkMath.RH.Weave.Analytic

/-!
# Eta unit-Gap normalization bridge

This module identifies the endpoint ratio-Gap with the existing reciprocal
unit split, then records the exact factor `m + 1` relating normalized and raw
eta amplitude Gaps.  The final decay theorem is deliberately only a raw
open-strip theorem; it does not promote raw decay to normalized decay.
-/

theorem etaEndpointIncrementMirrorGap_eq_etaMirrorUnitGap
    (s : ℂ) (m : ℕ) :
    etaEndpointIncrementMirrorGap s m = etaMirrorUnitGap s m := by
  rw [etaEndpointIncrementMirrorGap,
    etaEndpointIncrementMirrorRatio_eq_etaMirrorAmplitudeRatio]
  unfold etaMirrorUnitGap etaMirrorUnitPair UnitPair.gap
    unitAttachedCoreNeg
  have hpos : 0 < etaMirrorAmplitudeRatio s m :=
    etaMirrorAmplitudeRatio_pos s m
  have hsqrt : 0 < Real.sqrt (etaMirrorAmplitudeRatio s m) :=
    Real.sqrt_pos.2 hpos
  have hsq : (Real.sqrt (etaMirrorAmplitudeRatio s m)) ^ 2 =
      etaMirrorAmplitudeRatio s m :=
    Real.sq_sqrt hpos.le
  change etaMirrorAmplitudeRatio s m +
      (etaMirrorAmplitudeRatio s m)⁻¹ - 2 =
    (Real.sqrt (etaMirrorAmplitudeRatio s m) -
      (Real.sqrt (etaMirrorAmplitudeRatio s m))⁻¹) ^ 2
  field_simp [ne_of_gt hsqrt]
  rw [hsq]
  ring

/-- The genuine mirror and original eta magnitudes have product `1 / (m+1)`. -/
theorem etaMirrorAmplitudeProduct_eq_inv_succ
    (s : ℂ) (m : ℕ) :
    etaMirrorAmplitudeProduct s m = (((m + 1 : ℕ) : ℝ))⁻¹ := by
  rw [etaMirrorAmplitudeProduct_eq,
    norm_etaSignedVector_eq_rpow,
    norm_etaSignedVector_eq_rpow,
    criticalMirror_re]
  have hbase : 0 < (((m + 1 : ℕ) : ℝ)) := by positivity
  rw [← Real.rpow_add hbase]
  have hexp : (-(1 - s.re) + -s.re) = (-1 : ℝ) := by ring
  rw [hexp, Real.rpow_neg_one]

/-- Exact normalization: endpoint/unit Gap equals `(m+1)` times raw Gap. -/
theorem etaEndpointIncrementMirrorGap_eq_succ_mul_amplitudeGap
    (s : ℂ) (m : ℕ) :
    etaEndpointIncrementMirrorGap s m =
      ((m + 1 : ℕ) : ℝ) * etaMirrorAmplitudeGap s m := by
  rw [etaEndpointIncrementMirrorGap_eq_etaMirrorUnitGap]
  unfold etaMirrorUnitGap etaMirrorUnitPair UnitPair.gap
    unitAttachedCoreNeg
  rw [etaMirrorAmplitudeGap_eq]
  have hpos : 0 < etaMirrorAmplitudeRatio s m :=
    etaMirrorAmplitudeRatio_pos s m
  have hsqrt : 0 < Real.sqrt (etaMirrorAmplitudeRatio s m) :=
    Real.sqrt_pos.2 hpos
  have hsq : (Real.sqrt (etaMirrorAmplitudeRatio s m)) ^ 2 =
      etaMirrorAmplitudeRatio s m := Real.sq_sqrt hpos.le
  change (Real.sqrt (etaMirrorAmplitudeRatio s m) -
      (Real.sqrt (etaMirrorAmplitudeRatio s m))⁻¹) ^ 2 =
    ((m + 1 : ℕ) : ℝ) *
      (‖etaSignedVector (criticalMirror s) m‖ -
        ‖etaSignedVector s m‖) ^ 2
  rw [etaMirrorAmplitudeRatio]
  have hquotpos : 0 <
      ‖etaSignedVector (criticalMirror s) m‖ /
        ‖etaSignedVector s m‖ :=
    div_pos (norm_etaSignedVector_pos _ _) (norm_etaSignedVector_pos _ _)
  have hquot_sq :
      (Real.sqrt (‖etaSignedVector (criticalMirror s) m‖ /
        ‖etaSignedVector s m‖)) ^ 2 =
        ‖etaSignedVector (criticalMirror s) m‖ /
          ‖etaSignedVector s m‖ :=
    Real.sq_sqrt hquotpos.le
  have hprod := etaMirrorAmplitudeProduct_eq_inv_succ s m
  rw [etaMirrorAmplitudeProduct_eq] at hprod
  field_simp [ne_of_gt hsqrt,
    ne_of_gt (norm_etaSignedVector_pos s m)]
  rw [hquot_sq]
  have hq : ((m + 1 : ℕ) : ℝ) =
      (‖etaSignedVector (criticalMirror s) m‖ *
        ‖etaSignedVector s m‖)⁻¹ := by
    rw [hprod]
    simp
  rw [hq]
  field_simp [ne_of_gt (norm_etaSignedVector_pos s m),
    ne_of_gt (norm_etaSignedVector_pos (criticalMirror s) m)]

/-- Inverse form of the raw/normalized Gap scaling identity. -/
theorem etaMirrorAmplitudeGap_eq_inv_succ_mul_endpointGap
    (s : ℂ) (m : ℕ) :
    etaMirrorAmplitudeGap s m =
      (((m + 1 : ℕ) : ℝ))⁻¹ * etaEndpointIncrementMirrorGap s m := by
  rw [etaEndpointIncrementMirrorGap_eq_succ_mul_amplitudeGap]
  have hpos : 0 < (((m + 1 : ℕ) : ℝ)) := by positivity
  field_simp

/-- Finite weighted energy built from the unnormalized eta amplitude Gap. -/
noncomputable def etaMirrorAmplitudeGapEnergyUpTo
    (weight : ℕ → ℝ) (M : ℕ) (s : ℂ) : ℝ :=
  ∑ m ∈ Finset.range M, weight m * etaMirrorAmplitudeGap s m

/-- Endpoint energy equals raw amplitude energy with the `(m+1)` rescaling. -/
theorem etaEndpointIncrementMirrorEnergyUpTo_eq_rescaledAmplitudeGapEnergy
    (weight : ℕ → ℝ) (M : ℕ) (s : ℂ) :
    etaEndpointIncrementMirrorEnergyUpTo weight M s =
      etaMirrorAmplitudeGapEnergyUpTo
        (fun m => ((m + 1 : ℕ) : ℝ) * weight m) M s := by
  simp only [etaEndpointIncrementMirrorEnergyUpTo,
    etaMirrorAmplitudeGapEnergyUpTo]
  apply Finset.sum_congr rfl
  intro m hm
  rw [etaEndpointIncrementMirrorGap_eq_succ_mul_amplitudeGap]
  ring

/-- Raw amplitude Gap decays on the open strip, without a zero hypothesis. -/
theorem etaMirrorAmplitudeGap_tendsto_zero_of_openStrip
    {s : ℂ} (hleft : 0 < s.re) (hright : s.re < 1) :
    Tendsto (fun m : ℕ => etaMirrorAmplitudeGap s m) atTop (nhds 0) := by
  have hx : Tendsto (fun m : ℕ => ‖etaSignedVector s m‖)
      atTop (nhds 0) := by
    rw [show (0 : ℝ) = 0 from rfl]
    simpa only [norm_etaSignedVector_eq_rpow, Function.comp_def] using
      (tendsto_rpow_neg_atTop hleft).comp tendsto_nat_succ_cast_atTop
  have hmirror : 0 < (criticalMirror s).re := by
    rw [criticalMirror_re]
    linarith
  have hy : Tendsto (fun m : ℕ => ‖etaSignedVector (criticalMirror s) m‖)
      atTop (nhds 0) := by
    simpa only [norm_etaSignedVector_eq_rpow, Function.comp_def] using
      (tendsto_rpow_neg_atTop hmirror).comp tendsto_nat_succ_cast_atTop
  have hdiff := hy.sub hx
  simpa [etaMirrorAmplitudeGap, etaMirrorAmplitudePair] using hdiff.pow 2

end DkMath.RH.CFBRCProjection
