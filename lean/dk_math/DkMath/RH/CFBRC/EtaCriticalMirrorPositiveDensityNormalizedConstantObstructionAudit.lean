/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPositiveDensityBoundedSpanProjectionAudit
import Mathlib.Tactic

/-!
# ZDI-009: positive-density normalized constant obstruction

The current residual-majorant constants are strictly larger than the full
certified positive-density block-margin constants on both off-critical sides.
This module proves that scalar obstruction before any fixed-block projection
transport is attempted.  The conclusion concerns only the current bounds; it
does not estimate the exact oscillatory Eta tail.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.RH.Weave.Analytic

/--
Right-side scalar obstruction for the normalized residual-majorant route.
If `1/2 < σ < 1`, `0 < t`, `t ≤ n`, and `ρ > 0`, then the current right
residual constant is more than sixteen times the full certified margin
constant.  No projection-loss factor has been used in this inequality.
-/
theorem right_normalizedResidualConstant_gt_sixteen_mul_marginConstant
    {σ t n ρ : ℝ}
    (hσ : (1 : ℝ) / 2 < σ) (hσ1 : σ < 1)
    (ht : 0 < t) (hn : t ≤ n) (hρ : 0 < ρ) :
    16 * ((t ^ 2 / 4) * ρ * (1 + 2 * ρ) ^ (σ - 2)) <
      t * n / (1 - σ) * (2 / (1 + 2 * ρ)) ^ (1 - σ) := by
  let a : ℝ := 1 + 2 * ρ
  let R : ℝ := t * n / (1 - σ) * (2 / a) ^ (1 - σ)
  let M : ℝ := (t ^ 2 / 4) * ρ * a ^ (σ - 2)
  have ha : 0 < a := by
    dsimp [a]
    linarith
  have hden : 0 < 1 - σ := by
    linarith
  have hM : 0 < M := by
    dsimp [M]
    positivity
  have hnpos : 0 < n := lt_of_lt_of_le ht hn
  have hquot :
      R / M =
        4 * (n / t) * (1 / (1 - σ)) *
          (2 ^ (1 - σ)) * (a / ρ) := by
    have hid :
        ((2 / a) ^ (1 - σ)) / (a ^ (σ - 2)) =
          (2 ^ (1 - σ)) * a := by
      have hdiv :
          (2 / a) ^ (1 - σ) = 2 ^ (1 - σ) / a ^ (1 - σ) := by
        exact Real.div_rpow (by norm_num) ha.le _
      have hsum :
          a ^ (1 - σ) * a ^ (σ - 2) = a ^ (-1 : ℝ) := by
        rw [← Real.rpow_add ha]
        congr 1
        ring
      have hpow : a ^ (1 - σ) * a ^ (σ - 2) ≠ 0 := by
        positivity
      rw [hdiv]
      field_simp [hpow]
      rw [hsum]
      rw [Real.rpow_neg ha.le]
      field_simp
      rw [Real.rpow_one]
    dsimp [R, M]
    field_simp [hden.ne', ht.ne', hρ.ne']
    have hid' :
        (2 / a) ^ (1 - σ) =
          (2 ^ (1 - σ) * a) * a ^ (σ - 2) :=
      (div_eq_iff (Real.rpow_pos_of_pos ha _).ne').mp hid
    rw [hid']
    ring
  have hnratio : 1 ≤ n / t := by
    exact (le_div_iff₀ ht).2 (by simpa [one_mul] using hn)
  have hdenfactor : 2 < 1 / (1 - σ) := by
    apply (lt_div_iff₀ hden).2
    linarith
  have hpowfactor : 1 < (2 : ℝ) ^ (1 - σ) := by
    exact Real.one_lt_rpow (by norm_num) (by linarith)
  have haratio : 2 < a / ρ := by
    apply (lt_div_iff₀ hρ).2
    dsimp [a]
    linarith
  have hprod :
      16 < 4 * (n / t) * (1 / (1 - σ)) *
          (2 ^ (1 - σ)) * (a / ρ) := by
    have hA : 0 < 4 * (n / t) := by positivity
    have hB : 0 < 1 / (1 - σ) := by positivity
    have hC : 0 < (2 : ℝ) ^ (1 - σ) := by positivity
    have hB' : (2 : ℝ) < 1 / (1 - σ) := hdenfactor
    calc
      (16 : ℝ) = 4 * 2 * 1 * 2 := by norm_num
      _ ≤ 4 * (n / t) * 2 * 1 * 2 := by
        gcongr
        nlinarith [hnratio]
      _ < 4 * (n / t) * (1 / (1 - σ)) * 1 * 2 := by
        gcongr
      _ < 4 * (n / t) * (1 / (1 - σ)) *
            ((2 : ℝ) ^ (1 - σ)) * 2 := by
        gcongr
      _ < 4 * (n / t) * (1 / (1 - σ)) *
            ((2 : ℝ) ^ (1 - σ)) * (a / ρ) := by
        gcongr
  have hmain : 16 * M < R := by
    have hquot' : 16 < R / M := by
      rw [hquot]
      exact hprod
    exact (lt_div_iff₀ hM).mp hquot'
  simpa [R, M, a] using hmain

/--
Left-side scalar obstruction for the normalized residual-majorant route.
If `0 < σ < 1/2`, `0 < t`, `t ≤ n`, and `ρ > 0`, then the current left
residual constant is more than sixteen times the full certified margin
constant.
-/
theorem left_normalizedResidualConstant_gt_sixteen_mul_marginConstant
    {σ t n ρ : ℝ}
    (hσ : 0 < σ) (hσhalf : σ < (1 : ℝ) / 2)
    (ht : 0 < t) (hn : t ≤ n) (hρ : 0 < ρ) :
    16 * ((t ^ 2 / 4) * ρ * (1 + 2 * ρ) ^ (-σ - 1)) <
      t * n / σ * (2 / (1 + 2 * ρ)) ^ σ := by
  let a : ℝ := 1 + 2 * ρ
  let R : ℝ := t * n / σ * (2 / a) ^ σ
  let M : ℝ := (t ^ 2 / 4) * ρ * a ^ (-σ - 1)
  have ha : 0 < a := by
    dsimp [a]
    linarith
  have hM : 0 < M := by
    dsimp [M]
    positivity
  have hnpos : 0 < n := lt_of_lt_of_le ht hn
  have hquot :
      R / M =
        4 * (n / t) * (1 / σ) *
          (2 ^ σ) * (a / ρ) := by
    have hid :
        ((2 / a) ^ σ) / (a ^ (-σ - 1)) =
          (2 ^ σ) * a := by
      have hdiv :
          (2 / a) ^ σ = 2 ^ σ / a ^ σ := by
        exact Real.div_rpow (by norm_num) ha.le _
      have hsum :
          a ^ σ * a ^ (-σ - 1) = a ^ (-1 : ℝ) := by
        rw [← Real.rpow_add ha]
        congr 1
        ring
      have hpow : a ^ σ * a ^ (-σ - 1) ≠ 0 := by
        positivity
      rw [hdiv]
      field_simp [hpow]
      rw [hsum]
      rw [Real.rpow_neg ha.le]
      field_simp
      rw [Real.rpow_one]
    dsimp [R, M]
    field_simp [hσ.ne', ht.ne', hρ.ne']
    have hid' :
        (2 / a) ^ σ = (2 ^ σ * a) * a ^ (-σ - 1) :=
      (div_eq_iff (Real.rpow_pos_of_pos ha _).ne').mp hid
    rw [hid']
    ring
  have hnratio : 1 ≤ n / t := by
    exact (le_div_iff₀ ht).2 (by simpa [one_mul] using hn)
  have hσfactor : 2 < 1 / σ := by
    apply (lt_div_iff₀ hσ).2
    linarith
  have hpowfactor : 1 < (2 : ℝ) ^ σ := by
    exact Real.one_lt_rpow (by norm_num) hσ
  have haratio : 2 < a / ρ := by
    apply (lt_div_iff₀ hρ).2
    dsimp [a]
    linarith
  have hprod :
      16 < 4 * (n / t) * (1 / σ) *
          (2 ^ σ) * (a / ρ) := by
    have hA : 0 < 4 * (n / t) := by positivity
    have hB : 0 < 1 / σ := by positivity
    have hC : 0 < (2 : ℝ) ^ σ := by positivity
    calc
      (16 : ℝ) = 4 * 2 * 1 * 2 := by norm_num
      _ ≤ 4 * (n / t) * 2 * 1 * 2 := by
        gcongr
        nlinarith [hnratio]
      _ < 4 * (n / t) * (1 / σ) * 1 * 2 := by
        gcongr
      _ < 4 * (n / t) * (1 / σ) *
            ((2 : ℝ) ^ σ) * 2 := by
        gcongr
      _ < 4 * (n / t) * (1 / σ) *
            ((2 : ℝ) ^ σ) * (a / ρ) := by
        gcongr
  have hmain : 16 * M < R := by
    have hquot' : 16 < R / M := by
      rw [hquot]
      exact hprod
    exact (lt_div_iff₀ hM).mp hquot'
  simpa [R, M, a] using hmain

/-- The imaginary coordinate is bounded by the complex norm. -/
theorem abs_im_le_norm (s : ℂ) : |s.im| ≤ ‖s‖ :=
  Complex.abs_im_le_norm s

/-- The same norm bridge holds for the critical mirror. -/
theorem abs_im_le_norm_criticalMirror (s : ℂ) :
    |s.im| ≤ ‖criticalMirror s‖ := by
  simpa [criticalMirror_im] using Complex.abs_im_le_norm (criticalMirror s)

/--
Right-side specialization of the scalar obstruction to an arbitrary
off-critical complex point.  It uses only the elementary norm bridge, not a
zeta-zero hypothesis.
-/
theorem right_normalizedResidualConstant_gt_sixteen_mul_marginConstant_of_point
    {s : ℂ} (hσ : (1 : ℝ) / 2 < s.re) (hσ1 : s.re < 1)
    (him : s.im ≠ 0) (hρ : 0 < ρ) :
    16 * (((s.im : ℝ) ^ 2 / 4) * ρ *
        (1 + 2 * ρ) ^ (s.re - 2)) <
      |s.im| * ‖criticalMirror s‖ / (1 - s.re) *
      (2 / (1 + 2 * ρ)) ^ (1 - s.re) := by
  have h := right_normalizedResidualConstant_gt_sixteen_mul_marginConstant
    hσ hσ1 (abs_pos.mpr him) (abs_im_le_norm_criticalMirror s) hρ
  simpa [sq_abs] using h

/-- Left-side specialization of the scalar obstruction to an arbitrary point. -/
theorem left_normalizedResidualConstant_gt_sixteen_mul_marginConstant_of_point
    {s : ℂ} (hσ : 0 < s.re) (hσhalf : s.re < (1 : ℝ) / 2)
    (him : s.im ≠ 0) (hρ : 0 < ρ) :
    16 * (((s.im : ℝ) ^ 2 / 4) * ρ *
        (1 + 2 * ρ) ^ (-s.re - 1)) <
      |s.im| * ‖s‖ / s.re *
        (2 / (1 + 2 * ρ)) ^ s.re := by
  have h := left_normalizedResidualConstant_gt_sixteen_mul_marginConstant
    hσ hσhalf (abs_pos.mpr him) (abs_im_le_norm s) hρ
  simpa [sq_abs] using h

end DkMath.RH.CFBRCProjection
