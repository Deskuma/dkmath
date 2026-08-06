/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PrimeMirrorEtaBridge
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.PrimeMirrorEtaEnergyBridge"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.RH.Weave.Analytic

/-!
# Eta ratio-gap energy bridge

This layer reconstructs the prime-mirror offset Gap from the exact ratio of
adjacent eta endpoint increments.  It also lifts the pointwise identity to
finite weighted energies.  No zeta-zero or RH hypothesis is used here.
-/

/-- The ratio-only gap reconstructed from an eta endpoint increment. -/
noncomputable def etaEndpointIncrementMirrorGap (s : ℂ) (N : ℕ) : ℝ :=
  etaEndpointIncrementMirrorRatio s N +
    (etaEndpointIncrementMirrorRatio s N)⁻¹ - 2

/-- The endpoint ratio is strictly positive because both amplitudes are positive. -/
theorem etaEndpointIncrementMirrorRatio_pos (s : ℂ) (N : ℕ) :
    0 < etaEndpointIncrementMirrorRatio s N := by
  rw [etaEndpointIncrementMirrorRatio_eq_primeMirrorAmplitudeRatio]
  exact div_pos (primeMirrorRightAmplitude_pos _ _)
    (primeMirrorLeftAmplitude_pos _ _)

/-- The endpoint ratio-gap is exactly the prime-mirror square Gap. -/
theorem etaEndpointIncrementMirrorGap_eq_primeMirrorOffsetGap
    (s : ℂ) (N : ℕ) :
    etaEndpointIncrementMirrorGap s N =
      primeMirrorOffsetGap (N + 1) (centeredSigma s.re) := by
  let a := primeMirrorLeftAmplitude (N + 1) (centeredSigma s.re)
  let b := primeMirrorRightAmplitude (N + 1) (centeredSigma s.re)
  have ha : 0 < a := primeMirrorLeftAmplitude_pos _ _
  have hb : 0 < b := primeMirrorRightAmplitude_pos _ _
  have hab : a * b = 1 := primeMirrorAmplitude_mul_eq_one _ _
  rw [etaEndpointIncrementMirrorGap,
    etaEndpointIncrementMirrorRatio_eq_primeMirrorAmplitudeRatio]
  change b / a + (b / a)⁻¹ - 2 = (a - b) ^ 2
  field_simp [ne_of_gt ha]
  nlinarith

/-- The reconstructed endpoint Gap is nonnegative. -/
theorem etaEndpointIncrementMirrorGap_nonneg (s : ℂ) (N : ℕ) :
    0 ≤ etaEndpointIncrementMirrorGap s N := by
  rw [etaEndpointIncrementMirrorGap_eq_primeMirrorOffsetGap]
  exact primeMirrorOffsetGap_nonneg _ _

/-- At every nonconstant eta index, zero Gap is equivalent to the critical line. -/
theorem etaEndpointIncrementMirrorGap_eq_zero_iff_re_eq_half
    {N : ℕ} (hN : 0 < N) (s : ℂ) :
    etaEndpointIncrementMirrorGap s N = 0 ↔
      s.re = (1 : ℝ) / 2 := by
  rw [etaEndpointIncrementMirrorGap_eq_primeMirrorOffsetGap]
  rw [primeMirrorOffsetGap_eq_zero_iff_delta_eq_zero (by omega)]
  exact centeredSigma_eq_zero_iff s.re

/-- A noncritical real coordinate gives a strictly positive endpoint Gap. -/
theorem etaEndpointIncrementMirrorGap_pos_of_re_ne_half
    {N : ℕ} (hN : 0 < N) {s : ℂ}
    (hre : s.re ≠ (1 : ℝ) / 2) :
    0 < etaEndpointIncrementMirrorGap s N := by
  rw [etaEndpointIncrementMirrorGap_eq_primeMirrorOffsetGap]
  exact primeMirrorOffsetGap_pos_of_delta_ne_zero (by omega)
    ((centeredSigma_eq_zero_iff s.re).not.mpr hre)

/-- Finite weighted energy of endpoint ratio-Gaps through cutoff `M`. -/
noncomputable def etaEndpointIncrementMirrorEnergyUpTo
    (weight : ℕ → ℝ) (M : ℕ) (s : ℂ) : ℝ :=
  ∑ m ∈ Finset.range M, weight m * etaEndpointIncrementMirrorGap s m

/-- The same finite energy written directly in prime-mirror coordinates. -/
noncomputable def etaIndexedPrimeMirrorEnergyUpTo
    (weight : ℕ → ℝ) (M : ℕ) (s : ℂ) : ℝ :=
  ∑ m ∈ Finset.range M,
    weight m * primeMirrorOffsetGap (m + 1) (centeredSigma s.re)

/-- The eta-indexed and prime-mirror finite energies agree term by term. -/
theorem etaEndpointIncrementMirrorEnergyUpTo_eq_primeMirrorEnergy
    (weight : ℕ → ℝ) (M : ℕ) (s : ℂ) :
    etaEndpointIncrementMirrorEnergyUpTo weight M s =
      etaIndexedPrimeMirrorEnergyUpTo weight M s := by
  simp only [etaEndpointIncrementMirrorEnergyUpTo,
    etaIndexedPrimeMirrorEnergyUpTo]
  apply Finset.sum_congr rfl
  intro m hm
  rw [etaEndpointIncrementMirrorGap_eq_primeMirrorOffsetGap]

/-- A consecutive cutoff difference recovers the newly added eta mode. -/
@[simp] theorem etaEndpointIncrementMirrorEnergyUpTo_succ_sub
    (weight : ℕ → ℝ) (M : ℕ) (s : ℂ) :
    etaEndpointIncrementMirrorEnergyUpTo weight (M + 1) s -
        etaEndpointIncrementMirrorEnergyUpTo weight M s =
      weight M * etaEndpointIncrementMirrorGap s M := by
  simp only [etaEndpointIncrementMirrorEnergyUpTo, Finset.sum_range_succ]
  ring

/-- Successor cutoff energy is the previous energy plus one mode. -/
@[simp] theorem etaEndpointIncrementMirrorEnergyUpTo_succ_eq
    (weight : ℕ → ℝ) (M : ℕ) (s : ℂ) :
    etaEndpointIncrementMirrorEnergyUpTo weight (M + 1) s =
      etaEndpointIncrementMirrorEnergyUpTo weight M s +
        weight M * etaEndpointIncrementMirrorGap s M := by
  rw [← sub_eq_zero]
  simp only [etaEndpointIncrementMirrorEnergyUpTo, Finset.sum_range_succ]
  ring

/-- The base-two mode gives a lower bound for every nonnegative cutoff energy. -/
theorem etaEndpointIncrementMirrorEnergy_mode_one_le
    {weight : ℕ → ℝ} {M : ℕ} {s : ℂ}
    (hM : 2 ≤ M)
    (hweight : ∀ m < M, 0 ≤ weight m) :
    weight 1 * etaEndpointIncrementMirrorGap s 1 ≤
      etaEndpointIncrementMirrorEnergyUpTo weight M s := by
  apply Finset.single_le_sum (f := fun m ↦
    weight m * etaEndpointIncrementMirrorGap s m) (a := 1)
  · intro m hm
    exact mul_nonneg (hweight m (by simpa using hm))
      (etaEndpointIncrementMirrorGap_nonneg s m)
  · exact Finset.mem_range.mpr (by omega)

/-- A positive base-two weight forces finite energy positivity off the line. -/
theorem etaEndpointIncrementMirrorEnergy_pos_of_re_ne_half
    {weight : ℕ → ℝ} {M : ℕ} {s : ℂ}
    (hM : 2 ≤ M)
    (hweight : ∀ m < M, 0 ≤ weight m)
    (hweightOne : 0 < weight 1)
    (hre : s.re ≠ (1 : ℝ) / 2) :
    0 < etaEndpointIncrementMirrorEnergyUpTo weight M s := by
  have hle := etaEndpointIncrementMirrorEnergy_mode_one_le (s := s) hM hweight
  have hgap : 0 < etaEndpointIncrementMirrorGap s 1 :=
    etaEndpointIncrementMirrorGap_pos_of_re_ne_half (by omega) hre
  have hterm : 0 < weight 1 * etaEndpointIncrementMirrorGap s 1 :=
    mul_pos hweightOne hgap
  exact lt_of_lt_of_le hterm hle

end DkMath.RH.CFBRCProjection
