/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PrimeMirrorEtaNormalizationBridge
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.PrimeMirrorEtaAsymptoticDichotomy"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology
open DkMath.RH.Weave.Analytic

theorem primeMirrorOffsetGap_eq_rpow_pair
    {n : ℕ} (hn : 0 < n) (δ : ℝ) :
    primeMirrorOffsetGap n δ =
      ((n : ℝ) ^ (2 * δ)) + ((n : ℝ) ^ (-2 * δ)) - 2 := by
  have hbase : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [primeMirrorOffsetGap, primeMirrorLeftAmplitude,
    primeMirrorRightAmplitude, Real.rpow_def_of_pos hbase,
    Real.rpow_def_of_pos hbase]
  calc
    (Real.exp (-δ * Real.log (n : ℝ)) -
        Real.exp (δ * Real.log (n : ℝ))) ^ 2 =
      Real.exp (-δ * Real.log (n : ℝ)) ^ 2 +
        Real.exp (δ * Real.log (n : ℝ)) ^ 2 -
        2 * (Real.exp (-δ * Real.log (n : ℝ)) *
          Real.exp (δ * Real.log (n : ℝ))) := by ring
    _ = Real.exp (Real.log (n : ℝ) * (2 * δ)) +
        Real.exp (Real.log (n : ℝ) * (-2 * δ)) - 2 := by
      rw [show Real.exp (-δ * Real.log (n : ℝ)) ^ 2 =
          Real.exp ((-δ * Real.log (n : ℝ)) +
            (-δ * Real.log (n : ℝ))) by rw [pow_two, ← Real.exp_add],
        show Real.exp (δ * Real.log (n : ℝ)) ^ 2 =
          Real.exp ((δ * Real.log (n : ℝ)) +
            (δ * Real.log (n : ℝ))) by rw [pow_two, ← Real.exp_add],
        show Real.exp (-δ * Real.log (n : ℝ)) *
            Real.exp (δ * Real.log (n : ℝ)) = 1 by
          rw [← Real.exp_add]; ring_nf; simp]
      congr 1 <;> ring_nf

@[simp] theorem primeMirrorOffsetGap_neg_delta (n : ℕ) (δ : ℝ) :
    primeMirrorOffsetGap n (-δ) = primeMirrorOffsetGap n δ := by
  simp [primeMirrorOffsetGap, primeMirrorLeftAmplitude,
    primeMirrorRightAmplitude]
  ring

@[simp] theorem etaEndpointIncrementMirrorGap_criticalMirror
    (s : ℂ) (m : ℕ) :
    etaEndpointIncrementMirrorGap (criticalMirror s) m =
      etaEndpointIncrementMirrorGap s m := by
  rw [etaEndpointIncrementMirrorGap_eq_primeMirrorOffsetGap,
    etaEndpointIncrementMirrorGap_eq_primeMirrorOffsetGap,
    criticalMirror_re]
  rw [show centeredSigma (1 - s.re) = -centeredSigma s.re by
    unfold centeredSigma; ring]
  exact primeMirrorOffsetGap_neg_delta _ _

theorem etaEndpointIncrementMirrorGap_eq_rpow_pair
    (s : ℂ) (m : ℕ) :
    etaEndpointIncrementMirrorGap s m =
      (((m + 1 : ℕ) : ℝ) ^ (2 * centeredSigma s.re)) +
        (((m + 1 : ℕ) : ℝ) ^ (-2 * centeredSigma s.re)) - 2 := by
  rw [etaEndpointIncrementMirrorGap_eq_primeMirrorOffsetGap,
    primeMirrorOffsetGap_eq_rpow_pair (by positivity)]

theorem etaMirrorAmplitudeGap_eq_rpow_decomposition
    (s : ℂ) (m : ℕ) :
    etaMirrorAmplitudeGap s m =
      (((m + 1 : ℕ) : ℝ) ^ (-2 * s.re)) +
        (((m + 1 : ℕ) : ℝ) ^ (-2 * (1 - s.re))) -
        2 * (((m + 1 : ℕ) : ℝ)⁻¹) := by
  rw [etaMirrorAmplitudeGap_eq, norm_etaSignedVector_eq_rpow,
    norm_etaSignedVector_eq_rpow, criticalMirror_re]
  have hbase : 0 < (((m + 1 : ℕ) : ℝ)) := by positivity
  calc
    ((((m + 1 : ℕ) : ℝ) ^ (-(1 - s.re)) -
        ((m + 1 : ℕ) : ℝ) ^ (-s.re)) ^ 2) =
      (((m + 1 : ℕ) : ℝ) ^ (-(1 - s.re))) ^ 2 +
        (((m + 1 : ℕ) : ℝ) ^ (-s.re)) ^ 2 -
        2 * (((m + 1 : ℕ) : ℝ) ^ (-(1 - s.re)) *
          ((m + 1 : ℕ) : ℝ) ^ (-s.re)) := by ring
    _ = (((m + 1 : ℕ) : ℝ) ^ (-2 * s.re)) +
        (((m + 1 : ℕ) : ℝ) ^ (-2 * (1 - s.re))) -
        2 * (((m + 1 : ℕ) : ℝ)⁻¹) := by
      have hleft : (((m + 1 : ℕ) : ℝ) ^ (-s.re)) ^ 2 =
          ((m + 1 : ℕ) : ℝ) ^ (-2 * s.re) := by
        rw [pow_two, ← Real.rpow_add hbase]
        congr 1
        ring
      have hright : (((m + 1 : ℕ) : ℝ) ^ (-(1 - s.re))) ^ 2 =
          ((m + 1 : ℕ) : ℝ) ^ (-2 * (1 - s.re)) := by
        rw [pow_two, ← Real.rpow_add hbase]
        congr 1
        ring
      have hprod : (((m + 1 : ℕ) : ℝ) ^ (-(1 - s.re)) *
          ((m + 1 : ℕ) : ℝ) ^ (-s.re)) =
          (((m + 1 : ℕ) : ℝ)⁻¹) := by
        rw [← Real.rpow_add hbase]
        rw [show -(1 - s.re) + -s.re = (-1 : ℝ) by ring,
          Real.rpow_neg_one]
      rw [hleft, hright, hprod]
      ring

@[simp] theorem etaEndpointIncrementMirrorGap_eq_zero_of_re_eq_half
    {s : ℂ} (hre : s.re = (1 : ℝ) / 2) :
    ∀ m : ℕ, etaEndpointIncrementMirrorGap s m = 0 := by
  intro m
  cases m with
  | zero =>
      simp [etaEndpointIncrementMirrorGap,
        etaEndpointIncrementMirrorRatio_eq_etaMirrorAmplitudeRatio,
        etaMirrorAmplitudeRatio_eq_rpow]
      norm_num
  | succ m =>
      rw [etaEndpointIncrementMirrorGap_eq_zero_iff_re_eq_half (by omega)]
      exact hre

theorem etaEndpointIncrementMirrorGap_tendsto_zero_of_re_eq_half
    {s : ℂ} (hre : s.re = (1 : ℝ) / 2) :
    Tendsto (fun m : ℕ => etaEndpointIncrementMirrorGap s m) atTop (nhds 0) := by
  simp only [etaEndpointIncrementMirrorGap_eq_zero_of_re_eq_half hre]
  exact tendsto_const_nhds

theorem etaEndpointIncrementMirrorGap_tendsto_atTop_of_centeredSigma_pos
    {s : ℂ} (hδ : 0 < centeredSigma s.re) :
    Tendsto (fun m : ℕ => etaEndpointIncrementMirrorGap s m) atTop atTop := by
  have hpow : Tendsto (fun m : ℕ =>
      (((m + 1 : ℕ) : ℝ) ^ (2 * centeredSigma s.re))) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_nat_succ_cast_atTop
  rw [show (fun m : ℕ => etaEndpointIncrementMirrorGap s m) =
      (fun m => (((m + 1 : ℕ) : ℝ) ^ (2 * centeredSigma s.re)) +
        (((m + 1 : ℕ) : ℝ) ^ (-2 * centeredSigma s.re)) - 2) by
        funext m; exact etaEndpointIncrementMirrorGap_eq_rpow_pair s m]
  refine tendsto_atTop.2 ?_
  intro C
  filter_upwards [hpow.eventually_gt_atTop (C + 2)] with m hm
  have hnonneg : 0 ≤ (((m + 1 : ℕ) : ℝ) ^ (-2 * centeredSigma s.re)) :=
    Real.rpow_nonneg (by positivity) _
  linarith

theorem etaEndpointIncrementMirrorGap_tendsto_atTop_of_centeredSigma_neg
    {s : ℂ} (hδ : centeredSigma s.re < 0) :
    Tendsto (fun m : ℕ => etaEndpointIncrementMirrorGap s m) atTop atTop := by
  have hmirror : 0 < centeredSigma (criticalMirror s).re := by
    rw [criticalMirror_re]
    unfold centeredSigma at hδ ⊢
    linarith
  have h := etaEndpointIncrementMirrorGap_tendsto_atTop_of_centeredSigma_pos
    (s := criticalMirror s) hmirror
  refine h.congr' (Eventually.of_forall (fun m => ?_))
  rw [← etaEndpointIncrementMirrorGap_criticalMirror,
    criticalMirror_involutive]

theorem etaEndpointIncrementMirrorGap_tendsto_atTop_of_re_ne_half
    {s : ℂ} (hre : s.re ≠ (1 : ℝ) / 2) :
    Tendsto (fun m : ℕ => etaEndpointIncrementMirrorGap s m) atTop atTop := by
  have hδ : centeredSigma s.re ≠ 0 :=
    (centeredSigma_eq_zero_iff s.re).not.mpr hre
  rcases lt_or_gt_of_ne hδ with hneg | hpos
  · exact etaEndpointIncrementMirrorGap_tendsto_atTop_of_centeredSigma_neg hneg
  · exact etaEndpointIncrementMirrorGap_tendsto_atTop_of_centeredSigma_pos hpos

theorem etaEndpointIncrementMirrorGap_tendsto_zero_iff_re_eq_half
    (s : ℂ) :
    Tendsto (fun m : ℕ => etaEndpointIncrementMirrorGap s m) atTop (nhds 0) ↔
      s.re = (1 : ℝ) / 2 := by
  constructor
  · intro hlim
    by_contra hre
    exact not_tendsto_nhds_of_tendsto_atTop
      (etaEndpointIncrementMirrorGap_tendsto_atTop_of_re_ne_half hre)
      _ hlim
  · intro hre
    exact etaEndpointIncrementMirrorGap_tendsto_zero_of_re_eq_half hre

theorem etaMirrorAmplitudeGap_raw_zero_normalized_atTop
    {s : ℂ} (hleft : 0 < s.re) (hright : s.re < 1)
    (hre : s.re ≠ (1 : ℝ) / 2) :
    Tendsto (fun m : ℕ => etaMirrorAmplitudeGap s m) atTop (nhds 0) ∧
      Tendsto (fun m : ℕ =>
        ((m + 1 : ℕ) : ℝ) * etaMirrorAmplitudeGap s m) atTop atTop := by
  refine ⟨etaMirrorAmplitudeGap_tendsto_zero_of_openStrip hleft hright, ?_⟩
  have hnorm := etaEndpointIncrementMirrorGap_tendsto_atTop_of_re_ne_half hre
  refine hnorm.congr' (Eventually.of_forall (fun m => ?_))
  rw [etaEndpointIncrementMirrorGap_eq_succ_mul_amplitudeGap]

end DkMath.RH.CFBRCProjection
