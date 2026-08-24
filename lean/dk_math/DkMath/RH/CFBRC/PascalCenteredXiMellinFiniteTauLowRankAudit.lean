/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiMellinLowRankAudit
import Mathlib.Tactic

/-!
# Finite-`τ` low-rank Mellin separation

This module lifts the two- and three-orbit local Mellin jets to finite
nonzero dilation parameters.  The dilation values are fixed multiples of one
punctured parameter, so the resulting eventual statements are genuine
finite-evaluation separation results.  The Mellin spectral factor is handled
later by exact column scaling; no carrier-dependent weight is introduced.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open Filter

private theorem tendsto_kernel_quadratic_scaled
    (c : ℝ) (z : ℂ) :
    Tendsto
      (fun t : ℝ => complexExpSecondDifferenceKernel (c * t) z)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (z ^ 2)) := by
  have hscale : Tendsto (fun t : ℝ => c * t)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds 0) := by
    simpa using
      (tendsto_const_nhds.mul
        (Filter.tendsto_id.mono_left
          (nhdsWithin_le_nhds :
            nhdsWithin (0 : ℝ) ({0}ᶜ) ≤ nhds 0)))
  exact tendsto_complexExpSecondDifferenceKernel_quadraticJet z |>.comp hscale

/-! ## Common scaled jet transport -/

private theorem tendsto_kernel_quartic_scaled
    (c : ℝ) (hc : c ≠ 0) (z : ℂ) :
    Tendsto
      (fun t : ℝ =>
        (complexExpSecondDifferenceKernel (c * t) z - z ^ 2) /
          (t : ℂ) ^ 2)
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhds ((c : ℂ) ^ 2 * (z ^ 4 / 12))) := by
  have hscale : Tendsto (fun t : ℝ => c * t)
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · simpa using
        (tendsto_const_nhds.mul
          (Filter.tendsto_id.mono_left
            (nhdsWithin_le_nhds :
              nhdsWithin (0 : ℝ) ({0}ᶜ) ≤ nhds 0)))
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht
      exact Set.mem_compl_singleton_iff.mpr (mul_ne_zero hc ht0)
  have hbase :=
    tendsto_complexExpSecondDifferenceKernel_quarticJet z |>.comp hscale
  have hmul := hbase.mul_const ((c : ℂ) ^ 2)
  have hmul' : Tendsto
      (fun t : ℝ =>
        ((complexExpSecondDifferenceKernel (c * t) z - z ^ 2) /
          ((c * t : ℝ) : ℂ) ^ 2) * (c : ℂ) ^ 2)
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhds ((c : ℂ) ^ 2 * (z ^ 4 / 12))) := by
    simpa [Function.comp_def, mul_comm] using hmul
  apply hmul'.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht
  field_simp [ht0, hc]
  norm_num [Complex.ofReal_mul]
  ring_nf

private theorem tendsto_kernel_sextic_scaled
    (c : ℝ) (hc : c ≠ 0) (z : ℂ) :
    Tendsto
      (fun t : ℝ =>
        (complexExpSecondDifferenceKernel (c * t) z - z ^ 2 -
          (c * t : ℂ) ^ 2 * (z ^ 4 / 12)) /
          (t : ℂ) ^ 4)
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhds ((c : ℂ) ^ 4 * (z ^ 6 / 360))) := by
  have hscale : Tendsto (fun t : ℝ => c * t)
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · simpa using
        (tendsto_const_nhds.mul
          (Filter.tendsto_id.mono_left
            (nhdsWithin_le_nhds :
              nhdsWithin (0 : ℝ) ({0}ᶜ) ≤ nhds 0)))
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht
      exact Set.mem_compl_singleton_iff.mpr (mul_ne_zero hc ht0)
  have hbase :=
    tendsto_complexExpSecondDifferenceKernel_sexticJet z |>.comp hscale
  have hmul := hbase.mul_const ((c : ℂ) ^ 4)
  have hmul' : Tendsto
      (fun t : ℝ =>
        ((complexExpSecondDifferenceKernel (c * t) z - z ^ 2 -
          ((c * t : ℝ) : ℂ) ^ 2 * (z ^ 4 / 12)) /
          ((c * t : ℝ) : ℂ) ^ 4) * (c : ℂ) ^ 4)
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhds ((c : ℂ) ^ 4 * (z ^ 6 / 360))) := by
    simpa [Function.comp_def, mul_comm] using hmul
  apply hmul'.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht
  field_simp [ht0, hc]
  norm_num [Complex.ofReal_mul]
  ring_nf

/-! ## C0-A: two-orbit bare-kernel finite-`τ` separation -/

/-- The scalar two-orbit determinant evaluated at `(t, 2t)`. -/
noncomputable def bareTwoOrbitEvaluationDeterminant
    (t : ℝ) (z₁ z₂ : ℂ) : ℂ :=
  complexExpSecondDifferenceKernel t z₁ *
      complexExpSecondDifferenceKernel (2 * t) z₂ -
    complexExpSecondDifferenceKernel t z₂ *
      complexExpSecondDifferenceKernel (2 * t) z₁

/-- The normalized two-orbit evaluation determinant tends to three times the
previously proved two-orbit jet determinant. -/
theorem tendsto_bareTwoOrbitEvaluationDeterminant_normalized
    (z₁ z₂ : ℂ) :
    Tendsto
      (fun t : ℝ =>
        bareTwoOrbitEvaluationDeterminant t z₁ z₂ /
          (t : ℂ) ^ 2)
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhds (3 * (z₁ ^ 2 * ((z₂ ^ 2) ^ 2 / 12) -
        z₂ ^ 2 * ((z₁ ^ 2) ^ 2 / 12)))) := by
  let q₁ : ℂ := z₁ ^ 2
  let q₂ : ℂ := z₂ ^ 2
  let d₁ : ℂ := z₁ ^ 4 / 12
  let d₂ : ℂ := z₂ ^ 4 / 12
  have hK₁ : Tendsto
      (fun t : ℝ => complexExpSecondDifferenceKernel t z₁)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds q₁) := by
    simpa [q₁] using tendsto_kernel_quadratic_scaled 1 z₁
  have hK₂ : Tendsto
      (fun t : ℝ => complexExpSecondDifferenceKernel t z₂)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds q₂) := by
    simpa [q₂] using tendsto_kernel_quadratic_scaled 1 z₂
  have hA₁ : Tendsto
      (fun t : ℝ =>
        (complexExpSecondDifferenceKernel t z₁ - q₁) / (t : ℂ) ^ 2)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds d₁) := by
    simpa [q₁, d₁] using tendsto_kernel_quartic_scaled 1 one_ne_zero z₁
  have hA₂ : Tendsto
      (fun t : ℝ =>
        (complexExpSecondDifferenceKernel t z₂ - q₂) / (t : ℂ) ^ 2)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds d₂) := by
    simpa [q₂, d₂] using tendsto_kernel_quartic_scaled 1 one_ne_zero z₂
  have hB₁ : Tendsto
      (fun t : ℝ =>
        (complexExpSecondDifferenceKernel (2 * t) z₁ - q₁) /
          (t : ℂ) ^ 2)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (4 * d₁)) := by
    convert tendsto_kernel_quartic_scaled 2 (by norm_num) z₁ using 1
    norm_num [q₁, d₁]
  have hB₂ : Tendsto
      (fun t : ℝ =>
        (complexExpSecondDifferenceKernel (2 * t) z₂ - q₂) /
          (t : ℂ) ^ 2)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (4 * d₂)) := by
    convert tendsto_kernel_quartic_scaled 2 (by norm_num) z₂ using 1
    norm_num [q₂, d₂]
  have hcq₁ : Tendsto (fun _ : ℝ => q₁)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds q₁) := tendsto_const_nhds
  have hcq₂ : Tendsto (fun _ : ℝ => q₂)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds q₂) := tendsto_const_nhds
  have hsum : Tendsto
      (fun t : ℝ =>
        complexExpSecondDifferenceKernel t z₁ *
            ((complexExpSecondDifferenceKernel (2 * t) z₂ - q₂) /
              (t : ℂ) ^ 2) -
          complexExpSecondDifferenceKernel t z₂ *
            ((complexExpSecondDifferenceKernel (2 * t) z₁ - q₁) /
              (t : ℂ) ^ 2) +
          q₂ * ((complexExpSecondDifferenceKernel t z₁ - q₁) /
            (t : ℂ) ^ 2) -
          q₁ * ((complexExpSecondDifferenceKernel t z₂ - q₂) /
            (t : ℂ) ^ 2))
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhds (q₁ * (4 * d₂) - q₂ * (4 * d₁) +
        q₂ * d₁ - q₁ * d₂)) := by
    simpa [sub_eq_add_neg, add_assoc] using
      (((hK₁.mul hB₂).sub (hK₂.mul hB₁)).add
        ((hcq₂.mul hA₁).sub (hcq₁.mul hA₂)))
  have hsum' : Tendsto
      (fun t : ℝ =>
        complexExpSecondDifferenceKernel t z₁ *
            ((complexExpSecondDifferenceKernel (2 * t) z₂ - q₂) /
              (t : ℂ) ^ 2) -
          complexExpSecondDifferenceKernel t z₂ *
            ((complexExpSecondDifferenceKernel (2 * t) z₁ - q₁) /
              (t : ℂ) ^ 2) +
          q₂ * ((complexExpSecondDifferenceKernel t z₁ - q₁) /
            (t : ℂ) ^ 2) -
          q₁ * ((complexExpSecondDifferenceKernel t z₂ - q₂) /
            (t : ℂ) ^ 2))
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhds (3 * (z₁ ^ 2 * ((z₂ ^ 2) ^ 2 / 12) -
        z₂ ^ 2 * ((z₁ ^ 2) ^ 2 / 12)))) := by
    convert hsum using 1; simp [q₁, q₂, d₁, d₂]; ring
  apply hsum'.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht
  unfold bareTwoOrbitEvaluationDeterminant
  field_simp [ht0]
  ring

/-- Sufficiently small nonzero finite dilation parameters separate two
distinct nonzero squared coordinates for the bare Mellin kernel. -/
theorem eventually_bareTwoOrbitEvaluationDeterminant_ne_zero
    {z₁ z₂ : ℂ}
    (hq₁ : z₁ ^ 2 ≠ 0) (hq₂ : z₂ ^ 2 ≠ 0)
    (hsq : z₁ ^ 2 ≠ z₂ ^ 2) :
    ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) ({0}ᶜ),
      bareTwoOrbitEvaluationDeterminant t z₁ z₂ ≠ 0 := by
  have hD : z₁ ^ 2 * ((z₂ ^ 2) ^ 2 / 12) -
      z₂ ^ 2 * ((z₁ ^ 2) ^ 2 / 12) ≠ 0 :=
    twoOrbitMellinJetDeterminant_ne_zero hq₁ hq₂ hsq
  have hlimit :
      3 * (z₁ ^ 2 * ((z₂ ^ 2) ^ 2 / 12) -
        z₂ ^ 2 * ((z₁ ^ 2) ^ 2 / 12)) ≠ 0 :=
    mul_ne_zero (by norm_num) hD
  have hquot :=
    (tendsto_bareTwoOrbitEvaluationDeterminant_normalized z₁ z₂).eventually
      (eventually_ne_nhds hlimit)
  filter_upwards [hquot, self_mem_nhdsWithin] with t hquot ht
  intro hdet
  apply hquot
  rw [hdet]
  simp

/-! ## C0-B: three-orbit bare-kernel finite-`τ` separation -/

/-- The scalar three-orbit determinant evaluated at `(t, 2t, 3t)`. -/
noncomputable def bareThreeOrbitEvaluationDeterminant
    (t : ℝ) (z₁ z₂ z₃ : ℂ) : ℂ :=
  let k₁ := complexExpSecondDifferenceKernel t
  let k₂ := complexExpSecondDifferenceKernel (2 * t)
  let k₃ := complexExpSecondDifferenceKernel (3 * t)
  k₁ z₁ * (k₂ z₂ * k₃ z₃ - k₂ z₃ * k₃ z₂) -
    k₁ z₂ * (k₂ z₁ * k₃ z₃ - k₂ z₃ * k₃ z₁) +
    k₁ z₃ * (k₂ z₁ * k₃ z₂ - k₂ z₂ * k₃ z₁)

/-- The normalized three-orbit evaluation determinant tends to `120` times
the exact three-orbit jet determinant.  The coefficient `120` is obtained by
the fixed dilation values `1, 2, 3`, whose squared and quartic row
differences give `3`, `8`, and `40`. -/
theorem tendsto_bareThreeOrbitEvaluationDeterminant_normalized
    (z₁ z₂ z₃ : ℂ) :
    Tendsto
      (fun t : ℝ =>
        bareThreeOrbitEvaluationDeterminant t z₁ z₂ z₃ /
          (t : ℂ) ^ 6)
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhds (120 * (
        z₁ ^ 2 * ((z₂ ^ 4 / 12) * (z₃ ^ 6 / 360) -
            (z₃ ^ 4 / 12) * (z₂ ^ 6 / 360)) -
        z₂ ^ 2 * ((z₁ ^ 4 / 12) * (z₃ ^ 6 / 360) -
            (z₃ ^ 4 / 12) * (z₁ ^ 6 / 360)) +
        z₃ ^ 2 * ((z₁ ^ 4 / 12) * (z₂ ^ 6 / 360) -
            (z₂ ^ 4 / 12) * (z₁ ^ 6 / 360))))) := by
  let q₁ : ℂ := z₁ ^ 2
  let q₂ : ℂ := z₂ ^ 2
  let q₃ : ℂ := z₃ ^ 2
  let d₁ : ℂ := z₁ ^ 4 / 12
  let d₂ : ℂ := z₂ ^ 4 / 12
  let d₃ : ℂ := z₃ ^ 4 / 12
  let e₁ : ℂ := z₁ ^ 6 / 360
  let e₂ : ℂ := z₂ ^ 6 / 360
  let e₃ : ℂ := z₃ ^ 6 / 360
  have hK₁ : Tendsto (fun t : ℝ => complexExpSecondDifferenceKernel t z₁)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds q₁) := by
    simpa [q₁] using tendsto_kernel_quadratic_scaled 1 z₁
  have hK₂ : Tendsto (fun t : ℝ => complexExpSecondDifferenceKernel t z₂)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds q₂) := by
    simpa [q₂] using tendsto_kernel_quadratic_scaled 1 z₂
  have hK₃ : Tendsto (fun t : ℝ => complexExpSecondDifferenceKernel t z₃)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds q₃) := by
    simpa [q₃] using tendsto_kernel_quadratic_scaled 1 z₃
  have hA₁ := tendsto_kernel_quartic_scaled 1 one_ne_zero z₁
  have hA₂ := tendsto_kernel_quartic_scaled 1 one_ne_zero z₂
  have hA₃ := tendsto_kernel_quartic_scaled 1 one_ne_zero z₃
  have hB₁ := tendsto_kernel_quartic_scaled 2 (by norm_num) z₁
  have hB₂ := tendsto_kernel_quartic_scaled 2 (by norm_num) z₂
  have hB₃ := tendsto_kernel_quartic_scaled 2 (by norm_num) z₃
  have hC₁ := tendsto_kernel_quartic_scaled 3 (by norm_num) z₁
  have hC₂ := tendsto_kernel_quartic_scaled 3 (by norm_num) z₂
  have hC₃ := tendsto_kernel_quartic_scaled 3 (by norm_num) z₃
  have hE₁ := tendsto_kernel_sextic_scaled 1 one_ne_zero z₁
  have hE₂ := tendsto_kernel_sextic_scaled 1 one_ne_zero z₂
  have hE₃ := tendsto_kernel_sextic_scaled 1 one_ne_zero z₃
  have hF₁ := tendsto_kernel_sextic_scaled 2 (by norm_num) z₁
  have hF₂ := tendsto_kernel_sextic_scaled 2 (by norm_num) z₂
  have hF₃ := tendsto_kernel_sextic_scaled 2 (by norm_num) z₃
  have hG₁ := tendsto_kernel_sextic_scaled 3 (by norm_num) z₁
  have hG₂ := tendsto_kernel_sextic_scaled 3 (by norm_num) z₂
  have hG₃ := tendsto_kernel_sextic_scaled 3 (by norm_num) z₃
  have hu₁ : Tendsto (fun t : ℝ =>
      ((complexExpSecondDifferenceKernel (2 * t) z₁ - q₁) -
        (complexExpSecondDifferenceKernel t z₁ - q₁)) / (t : ℂ) ^ 2)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (3 * d₁)) := by
    convert (hB₁.sub hA₁) using 1 <;> (try funext t) <;>
      norm_num [q₁, d₁] <;> ring
  have hu₂ : Tendsto (fun t : ℝ =>
      ((complexExpSecondDifferenceKernel (2 * t) z₂ - q₂) -
        (complexExpSecondDifferenceKernel t z₂ - q₂)) / (t : ℂ) ^ 2)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (3 * d₂)) := by
    convert (hB₂.sub hA₂) using 1 <;> (try funext t) <;>
      norm_num [q₂, d₂] <;> ring
  have hu₃ : Tendsto (fun t : ℝ =>
      ((complexExpSecondDifferenceKernel (2 * t) z₃ - q₃) -
        (complexExpSecondDifferenceKernel t z₃ - q₃)) / (t : ℂ) ^ 2)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (3 * d₃)) := by
    convert (hB₃.sub hA₃) using 1 <;> (try funext t) <;>
      norm_num [q₃, d₃] <;> ring
  have hv₁ : Tendsto (fun t : ℝ =>
      ((complexExpSecondDifferenceKernel (3 * t) z₁ - q₁) -
        (complexExpSecondDifferenceKernel t z₁ - q₁)) / (t : ℂ) ^ 2)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (8 * d₁)) := by
    convert (hC₁.sub hA₁) using 1 <;> (try funext t) <;>
      norm_num [q₁, d₁] <;> ring
  have hv₂ : Tendsto (fun t : ℝ =>
      ((complexExpSecondDifferenceKernel (3 * t) z₂ - q₂) -
        (complexExpSecondDifferenceKernel t z₂ - q₂)) / (t : ℂ) ^ 2)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (8 * d₂)) := by
    convert (hC₂.sub hA₂) using 1 <;> (try funext t) <;>
      norm_num [q₂, d₂] <;> ring
  have hv₃ : Tendsto (fun t : ℝ =>
      ((complexExpSecondDifferenceKernel (3 * t) z₃ - q₃) -
        (complexExpSecondDifferenceKernel t z₃ - q₃)) / (t : ℂ) ^ 2)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (8 * d₃)) := by
    convert (hC₃.sub hA₃) using 1 <;> (try funext t) <;>
      norm_num [q₃, d₃] <;> ring
  have hw₁' : Tendsto (fun t : ℝ =>
      ((complexExpSecondDifferenceKernel (3 * t) z₁ - q₁ -
          ((3 : ℂ) * (t : ℂ)) ^ 2 * d₁) / (t : ℂ) ^ 4) -
        (8 / 3 : ℂ) *
          ((complexExpSecondDifferenceKernel (2 * t) z₁ - q₁ -
            ((2 : ℂ) * (t : ℂ)) ^ 2 * d₁) / (t : ℂ) ^ 4) +
        (5 / 3 : ℂ) *
          ((complexExpSecondDifferenceKernel t z₁ - q₁ -
            (t : ℂ) ^ 2 * d₁) / (t : ℂ) ^ 4))
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (40 * e₁)) := by
    convert (hG₁.sub (hF₁.const_mul ((8 / 3 : ℂ)))).add
      (hE₁.const_mul ((5 / 3 : ℂ))) using 1 <;>
      simp [q₁, d₁, e₁]; ring
  have hw₂' : Tendsto (fun t : ℝ =>
      ((complexExpSecondDifferenceKernel (3 * t) z₂ - q₂ -
          ((3 : ℂ) * (t : ℂ)) ^ 2 * d₂) / (t : ℂ) ^ 4) -
        (8 / 3 : ℂ) *
          ((complexExpSecondDifferenceKernel (2 * t) z₂ - q₂ -
            ((2 : ℂ) * (t : ℂ)) ^ 2 * d₂) / (t : ℂ) ^ 4) +
        (5 / 3 : ℂ) *
          ((complexExpSecondDifferenceKernel t z₂ - q₂ -
            (t : ℂ) ^ 2 * d₂) / (t : ℂ) ^ 4))
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (40 * e₂)) := by
    convert (hG₂.sub (hF₂.const_mul ((8 / 3 : ℂ)))).add
      (hE₂.const_mul ((5 / 3 : ℂ))) using 1 <;>
      simp [q₂, d₂, e₂]; ring
  have hw₃' : Tendsto (fun t : ℝ =>
      ((complexExpSecondDifferenceKernel (3 * t) z₃ - q₃ -
          ((3 : ℂ) * (t : ℂ)) ^ 2 * d₃) / (t : ℂ) ^ 4) -
        (8 / 3 : ℂ) *
          ((complexExpSecondDifferenceKernel (2 * t) z₃ - q₃ -
            ((2 : ℂ) * (t : ℂ)) ^ 2 * d₃) / (t : ℂ) ^ 4) +
        (5 / 3 : ℂ) *
          ((complexExpSecondDifferenceKernel t z₃ - q₃ -
            (t : ℂ) ^ 2 * d₃) / (t : ℂ) ^ 4))
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (40 * e₃)) := by
    convert (hG₃.sub (hF₃.const_mul ((8 / 3 : ℂ)))).add
      (hE₃.const_mul ((5 / 3 : ℂ))) using 1 <;>
      simp [q₃, d₃, e₃]; ring
  have hw₁ : Tendsto (fun t : ℝ =>
      (((complexExpSecondDifferenceKernel (3 * t) z₁ - q₁) -
          (complexExpSecondDifferenceKernel t z₁ - q₁)) / (t : ℂ) ^ 2 -
        (8 / 3 : ℂ) * (((complexExpSecondDifferenceKernel (2 * t) z₁ - q₁) -
          (complexExpSecondDifferenceKernel t z₁ - q₁)) / (t : ℂ) ^ 2)) /
        (t : ℂ) ^ 2)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (40 * e₁)) := by
    apply hw₁'.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht
    field_simp [ht0]
    ring_nf
  have hw₂ : Tendsto (fun t : ℝ =>
      (((complexExpSecondDifferenceKernel (3 * t) z₂ - q₂) -
          (complexExpSecondDifferenceKernel t z₂ - q₂)) / (t : ℂ) ^ 2 -
        (8 / 3 : ℂ) * (((complexExpSecondDifferenceKernel (2 * t) z₂ - q₂) -
          (complexExpSecondDifferenceKernel t z₂ - q₂)) / (t : ℂ) ^ 2)) /
        (t : ℂ) ^ 2)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (40 * e₂)) := by
    apply hw₂'.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht
    field_simp [ht0]
    ring
  have hw₃ : Tendsto (fun t : ℝ =>
      (((complexExpSecondDifferenceKernel (3 * t) z₃ - q₃) -
          (complexExpSecondDifferenceKernel t z₃ - q₃)) / (t : ℂ) ^ 2 -
        (8 / 3 : ℂ) * (((complexExpSecondDifferenceKernel (2 * t) z₃ - q₃) -
          (complexExpSecondDifferenceKernel t z₃ - q₃)) / (t : ℂ) ^ 2)) /
        (t : ℂ) ^ 2)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (40 * e₃)) := by
    apply hw₃'.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht
    field_simp [ht0]
    ring
  have hrow : Tendsto (fun t : ℝ =>
      complexExpSecondDifferenceKernel t z₁ * (
        (((complexExpSecondDifferenceKernel (2 * t) z₂ - q₂) -
            (complexExpSecondDifferenceKernel t z₂ - q₂)) / (t : ℂ) ^ 2) *
          (((complexExpSecondDifferenceKernel (3 * t) z₃ - q₃) -
            (complexExpSecondDifferenceKernel t z₃ - q₃)) / (t : ℂ) ^ 2 -
            (8 / 3 : ℂ) * (((complexExpSecondDifferenceKernel (2 * t) z₃ - q₃) -
              (complexExpSecondDifferenceKernel t z₃ - q₃)) / (t : ℂ) ^ 2)) /
            (t : ℂ) ^ 2 -
          (((complexExpSecondDifferenceKernel (3 * t) z₂ - q₂) -
            (complexExpSecondDifferenceKernel t z₂ - q₂)) / (t : ℂ) ^ 2 -
            (8 / 3 : ℂ) * (((complexExpSecondDifferenceKernel (2 * t) z₂ - q₂) -
              (complexExpSecondDifferenceKernel t z₂ - q₂)) / (t : ℂ) ^ 2)) /
            (t : ℂ) ^ 2 *
          (((complexExpSecondDifferenceKernel (2 * t) z₃ - q₃) -
            (complexExpSecondDifferenceKernel t z₃ - q₃)) / (t : ℂ) ^ 2)) -
        complexExpSecondDifferenceKernel t z₂ * (
        (((complexExpSecondDifferenceKernel (2 * t) z₁ - q₁) -
            (complexExpSecondDifferenceKernel t z₁ - q₁)) / (t : ℂ) ^ 2) *
          (((complexExpSecondDifferenceKernel (3 * t) z₃ - q₃) -
            (complexExpSecondDifferenceKernel t z₃ - q₃)) / (t : ℂ) ^ 2 -
            (8 / 3 : ℂ) * (((complexExpSecondDifferenceKernel (2 * t) z₃ - q₃) -
              (complexExpSecondDifferenceKernel t z₃ - q₃)) / (t : ℂ) ^ 2)) /
            (t : ℂ) ^ 2 -
          (((complexExpSecondDifferenceKernel (3 * t) z₁ - q₁) -
            (complexExpSecondDifferenceKernel t z₁ - q₁)) / (t : ℂ) ^ 2 -
            (8 / 3 : ℂ) * (((complexExpSecondDifferenceKernel (2 * t) z₁ - q₁) -
              (complexExpSecondDifferenceKernel t z₁ - q₁)) / (t : ℂ) ^ 2)) /
            (t : ℂ) ^ 2 *
          (((complexExpSecondDifferenceKernel (2 * t) z₃ - q₃) -
            (complexExpSecondDifferenceKernel t z₃ - q₃)) / (t : ℂ) ^ 2)) +
        complexExpSecondDifferenceKernel t z₃ * (
        (((complexExpSecondDifferenceKernel (2 * t) z₁ - q₁) -
            (complexExpSecondDifferenceKernel t z₁ - q₁)) / (t : ℂ) ^ 2) *
          (((complexExpSecondDifferenceKernel (3 * t) z₂ - q₂) -
            (complexExpSecondDifferenceKernel t z₂ - q₂)) / (t : ℂ) ^ 2 -
            (8 / 3 : ℂ) * (((complexExpSecondDifferenceKernel (2 * t) z₂ - q₂) -
              (complexExpSecondDifferenceKernel t z₂ - q₂)) / (t : ℂ) ^ 2)) /
            (t : ℂ) ^ 2 -
          (((complexExpSecondDifferenceKernel (3 * t) z₁ - q₁) -
            (complexExpSecondDifferenceKernel t z₁ - q₁)) / (t : ℂ) ^ 2 -
            (8 / 3 : ℂ) * (((complexExpSecondDifferenceKernel (2 * t) z₁ - q₁) -
              (complexExpSecondDifferenceKernel t z₁ - q₁)) / (t : ℂ) ^ 2)) /
            (t : ℂ) ^ 2 *
          (((complexExpSecondDifferenceKernel (2 * t) z₂ - q₂) -
            (complexExpSecondDifferenceKernel t z₂ - q₂)) / (t : ℂ) ^ 2)))
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhds (q₁ * ((3 * d₂) * (40 * e₃) - (3 * d₃) * (40 * e₂)) -
        q₂ * ((3 * d₁) * (40 * e₃) - (3 * d₃) * (40 * e₁)) +
        q₃ * ((3 * d₁) * (40 * e₂) - (3 * d₂) * (40 * e₁)))) := by
    convert (((hK₁.mul ((hu₂.mul hw₃).sub (hu₃.mul hw₂))).sub
        (hK₂.mul ((hu₁.mul hw₃).sub (hu₃.mul hw₁)))).add
        (hK₃.mul ((hu₁.mul hw₂).sub (hu₂.mul hw₁)))) using 1; (try funext t); ring
  have hrow' : Tendsto (fun t : ℝ =>
      complexExpSecondDifferenceKernel t z₁ * (
        (((complexExpSecondDifferenceKernel (2 * t) z₂ - q₂) -
            (complexExpSecondDifferenceKernel t z₂ - q₂)) / (t : ℂ) ^ 2) *
          (((complexExpSecondDifferenceKernel (3 * t) z₃ - q₃) -
            (complexExpSecondDifferenceKernel t z₃ - q₃)) / (t : ℂ) ^ 2 -
            (8 / 3 : ℂ) * (((complexExpSecondDifferenceKernel (2 * t) z₃ - q₃) -
              (complexExpSecondDifferenceKernel t z₃ - q₃)) / (t : ℂ) ^ 2)) /
            (t : ℂ) ^ 2 -
          (((complexExpSecondDifferenceKernel (3 * t) z₂ - q₂) -
            (complexExpSecondDifferenceKernel t z₂ - q₂)) / (t : ℂ) ^ 2 -
            (8 / 3 : ℂ) * (((complexExpSecondDifferenceKernel (2 * t) z₂ - q₂) -
              (complexExpSecondDifferenceKernel t z₂ - q₂)) / (t : ℂ) ^ 2)) /
            (t : ℂ) ^ 2 *
          (((complexExpSecondDifferenceKernel (2 * t) z₃ - q₃) -
            (complexExpSecondDifferenceKernel t z₃ - q₃)) / (t : ℂ) ^ 2)) -
        complexExpSecondDifferenceKernel t z₂ * (
        (((complexExpSecondDifferenceKernel (2 * t) z₁ - q₁) -
            (complexExpSecondDifferenceKernel t z₁ - q₁)) / (t : ℂ) ^ 2) *
          (((complexExpSecondDifferenceKernel (3 * t) z₃ - q₃) -
            (complexExpSecondDifferenceKernel t z₃ - q₃)) / (t : ℂ) ^ 2 -
            (8 / 3 : ℂ) * (((complexExpSecondDifferenceKernel (2 * t) z₃ - q₃) -
              (complexExpSecondDifferenceKernel t z₃ - q₃)) / (t : ℂ) ^ 2)) /
            (t : ℂ) ^ 2 -
          (((complexExpSecondDifferenceKernel (3 * t) z₁ - q₁) -
            (complexExpSecondDifferenceKernel t z₁ - q₁)) / (t : ℂ) ^ 2 -
            (8 / 3 : ℂ) * (((complexExpSecondDifferenceKernel (2 * t) z₁ - q₁) -
              (complexExpSecondDifferenceKernel t z₁ - q₁)) / (t : ℂ) ^ 2)) /
            (t : ℂ) ^ 2 *
          (((complexExpSecondDifferenceKernel (2 * t) z₃ - q₃) -
            (complexExpSecondDifferenceKernel t z₃ - q₃)) / (t : ℂ) ^ 2)) +
        complexExpSecondDifferenceKernel t z₃ * (
        (((complexExpSecondDifferenceKernel (2 * t) z₁ - q₁) -
            (complexExpSecondDifferenceKernel t z₁ - q₁)) / (t : ℂ) ^ 2) *
          (((complexExpSecondDifferenceKernel (3 * t) z₂ - q₂) -
            (complexExpSecondDifferenceKernel t z₂ - q₂)) / (t : ℂ) ^ 2 -
            (8 / 3 : ℂ) * (((complexExpSecondDifferenceKernel (2 * t) z₂ - q₂) -
              (complexExpSecondDifferenceKernel t z₂ - q₂)) / (t : ℂ) ^ 2)) /
            (t : ℂ) ^ 2 -
          (((complexExpSecondDifferenceKernel (3 * t) z₁ - q₁) -
            (complexExpSecondDifferenceKernel t z₁ - q₁)) / (t : ℂ) ^ 2 -
            (8 / 3 : ℂ) * (((complexExpSecondDifferenceKernel (2 * t) z₁ - q₁) -
              (complexExpSecondDifferenceKernel t z₁ - q₁)) / (t : ℂ) ^ 2)) /
            (t : ℂ) ^ 2 *
          (((complexExpSecondDifferenceKernel (2 * t) z₂ - q₂) -
            (complexExpSecondDifferenceKernel t z₂ - q₂)) / (t : ℂ) ^ 2)))
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhds (120 * (
        z₁ ^ 2 * ((z₂ ^ 4 / 12) * (z₃ ^ 6 / 360) -
            (z₃ ^ 4 / 12) * (z₂ ^ 6 / 360)) -
        z₂ ^ 2 * ((z₁ ^ 4 / 12) * (z₃ ^ 6 / 360) -
            (z₃ ^ 4 / 12) * (z₁ ^ 6 / 360)) +
        z₃ ^ 2 * ((z₁ ^ 4 / 12) * (z₂ ^ 6 / 360) -
            (z₂ ^ 4 / 12) * (z₁ ^ 6 / 360))))) := by
    have hcoeff :
        q₁ * ((3 * d₂) * (40 * e₃) - (3 * d₃) * (40 * e₂)) -
            q₂ * ((3 * d₁) * (40 * e₃) - (3 * d₃) * (40 * e₁)) +
            q₃ * ((3 * d₁) * (40 * e₂) - (3 * d₂) * (40 * e₁)) =
          120 * (z₁ ^ 2 * ((z₂ ^ 4 / 12) * (z₃ ^ 6 / 360) -
              (z₃ ^ 4 / 12) * (z₂ ^ 6 / 360)) -
            z₂ ^ 2 * ((z₁ ^ 4 / 12) * (z₃ ^ 6 / 360) -
              (z₃ ^ 4 / 12) * (z₁ ^ 6 / 360)) +
            z₃ ^ 2 * ((z₁ ^ 4 / 12) * (z₂ ^ 6 / 360) -
              (z₂ ^ 4 / 12) * (z₁ ^ 6 / 360))) := by
      dsimp [q₁, q₂, q₃, d₁, d₂, d₃, e₁, e₂, e₃]
      ring
    rw [hcoeff] at hrow
    convert hrow using 1
  apply hrow'.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht
  unfold bareThreeOrbitEvaluationDeterminant
  dsimp
  field_simp [ht0]
  ring

/-- Sufficiently small nonzero finite dilation parameters separate three
distinct nonzero squared coordinates for the bare Mellin kernel. -/
theorem eventually_bareThreeOrbitEvaluationDeterminant_ne_zero
    {z₁ z₂ z₃ : ℂ}
    (hq₁ : z₁ ^ 2 ≠ 0) (hq₂ : z₂ ^ 2 ≠ 0) (hq₃ : z₃ ^ 2 ≠ 0)
    (h₁₂ : z₁ ^ 2 ≠ z₂ ^ 2) (h₁₃ : z₁ ^ 2 ≠ z₃ ^ 2)
    (h₂₃ : z₂ ^ 2 ≠ z₃ ^ 2) :
    ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) ({0}ᶜ),
      bareThreeOrbitEvaluationDeterminant t z₁ z₂ z₃ ≠ 0 := by
  have hD := threeOrbitMellinJetDeterminant_ne_zero hq₁ hq₂ hq₃ h₁₂ h₁₃ h₂₃
  have hlimit :
      120 * (z₁ ^ 2 * ((z₂ ^ 4 / 12) * (z₃ ^ 6 / 360) -
          (z₃ ^ 4 / 12) * (z₂ ^ 6 / 360)) -
        z₂ ^ 2 * ((z₁ ^ 4 / 12) * (z₃ ^ 6 / 360) -
          (z₃ ^ 4 / 12) * (z₁ ^ 6 / 360)) +
        z₃ ^ 2 * ((z₁ ^ 4 / 12) * (z₂ ^ 6 / 360) -
          (z₂ ^ 4 / 12) * (z₁ ^ 6 / 360))) ≠ 0 := by
    have hnon := mul_ne_zero (by norm_num : (120 : ℂ) ≠ 0) hD
    convert hnon using 1; ring
  have hquot :=
    (tendsto_bareThreeOrbitEvaluationDeterminant_normalized z₁ z₂ z₃).eventually
      (eventually_ne_nhds hlimit)
  filter_upwards [hquot, self_mem_nhdsWithin] with t hquot ht
  intro hdet
  apply hquot
  rw [hdet]
  simp

/-! ## C0-C: exact spectral-factor column scaling -/

/-- The actual Mellin two-orbit determinant is the bare determinant with one
spectral factor attached to each column.  The factors are retained exactly;
they are not normalized away. -/
noncomputable def mellinTwoOrbitEvaluationDeterminant
    (ε t : ℝ) (z₁ z₂ : ℂ) : ℂ :=
  pascalCenteredXiMellinSecondDifferenceWeight ε t z₁ *
      pascalCenteredXiMellinSecondDifferenceWeight ε (2 * t) z₂ -
    pascalCenteredXiMellinSecondDifferenceWeight ε t z₂ *
      pascalCenteredXiMellinSecondDifferenceWeight ε (2 * t) z₁

/-- Exact two-column spectral-factorization identity at nonzero finite `τ`. -/
theorem mellinTwoOrbitEvaluationDeterminant_eq_spectral_mul_bare
    {ε t : ℝ} (ht : t ≠ 0) (z₁ z₂ : ℂ) :
    mellinTwoOrbitEvaluationDeterminant ε t z₁ z₂ =
      centeredMellinSpectralWeight (centeredMellinBoxApprox ε) z₁ *
          centeredMellinSpectralWeight (centeredMellinBoxApprox ε) z₂ *
        bareTwoOrbitEvaluationDeterminant t z₁ z₂ := by
  unfold mellinTwoOrbitEvaluationDeterminant
  rw [pascalCenteredXiMellinSecondDifferenceWeight_eq_kernel_mul ht,
    pascalCenteredXiMellinSecondDifferenceWeight_eq_kernel_mul
      (mul_ne_zero (by norm_num) ht)]
  rw [pascalCenteredXiMellinSecondDifferenceWeight_eq_kernel_mul ht,
    pascalCenteredXiMellinSecondDifferenceWeight_eq_kernel_mul
      (mul_ne_zero (by norm_num) ht)]
  unfold bareTwoOrbitEvaluationDeterminant
  simp [complexExpSecondDifferenceKernel, ht, Complex.ofReal_mul]
  ring

/-- The actual Mellin three-orbit determinant is the bare determinant with one
spectral factor attached to each column. -/
noncomputable def mellinThreeOrbitEvaluationDeterminant
    (ε t : ℝ) (z₁ z₂ z₃ : ℂ) : ℂ :=
  let k₁ := pascalCenteredXiMellinSecondDifferenceWeight ε t
  let k₂ := pascalCenteredXiMellinSecondDifferenceWeight ε (2 * t)
  let k₃ := pascalCenteredXiMellinSecondDifferenceWeight ε (3 * t)
  k₁ z₁ * (k₂ z₂ * k₃ z₃ - k₂ z₃ * k₃ z₂) -
    k₁ z₂ * (k₂ z₁ * k₃ z₃ - k₂ z₃ * k₃ z₁) +
    k₁ z₃ * (k₂ z₁ * k₃ z₂ - k₂ z₂ * k₃ z₁)

/-- Exact three-column spectral-factorization identity at nonzero finite `τ`.
The dilation parameters are precisely `t`, `2t`, and `3t`. -/
theorem mellinThreeOrbitEvaluationDeterminant_eq_spectral_mul_bare
    {ε t : ℝ} (ht : t ≠ 0) (z₁ z₂ z₃ : ℂ) :
    mellinThreeOrbitEvaluationDeterminant ε t z₁ z₂ z₃ =
      centeredMellinSpectralWeight (centeredMellinBoxApprox ε) z₁ *
          (centeredMellinSpectralWeight (centeredMellinBoxApprox ε) z₂ *
            centeredMellinSpectralWeight (centeredMellinBoxApprox ε) z₃) *
        bareThreeOrbitEvaluationDeterminant t z₁ z₂ z₃ := by
  have h2 : 2 * t ≠ 0 := mul_ne_zero (by norm_num) ht
  have h3 : 3 * t ≠ 0 := mul_ne_zero (by norm_num) ht
  unfold mellinThreeOrbitEvaluationDeterminant
  dsimp
  have h₁ (z : ℂ) :=
    pascalCenteredXiMellinSecondDifferenceWeight_eq_kernel_mul (ε := ε) (τ := t) ht z
  have h₂ (z : ℂ) :=
    pascalCenteredXiMellinSecondDifferenceWeight_eq_kernel_mul
      (ε := ε) (τ := 2 * t) h2 z
  have h₃ (z : ℂ) :=
    pascalCenteredXiMellinSecondDifferenceWeight_eq_kernel_mul
      (ε := ε) (τ := 3 * t) h3 z
  simp_rw [h₁, h₂, h₃]
  let S₁ : ℂ := centeredMellinSpectralWeight (centeredMellinBoxApprox ε) z₁
  let S₂ : ℂ := centeredMellinSpectralWeight (centeredMellinBoxApprox ε) z₂
  let S₃ : ℂ := centeredMellinSpectralWeight (centeredMellinBoxApprox ε) z₃
  have hdet :
      (complexExpSecondDifferenceKernel t z₁ * S₁) *
          ((complexExpSecondDifferenceKernel (2 * t) z₂ * S₂) *
              (complexExpSecondDifferenceKernel (3 * t) z₃ * S₃) -
            (complexExpSecondDifferenceKernel (2 * t) z₃ * S₃) *
              (complexExpSecondDifferenceKernel (3 * t) z₂ * S₂)) -
        (complexExpSecondDifferenceKernel t z₂ * S₂) *
          ((complexExpSecondDifferenceKernel (2 * t) z₁ * S₁) *
              (complexExpSecondDifferenceKernel (3 * t) z₃ * S₃) -
            (complexExpSecondDifferenceKernel (2 * t) z₃ * S₃) *
              (complexExpSecondDifferenceKernel (3 * t) z₁ * S₁)) +
        (complexExpSecondDifferenceKernel t z₃ * S₃) *
          ((complexExpSecondDifferenceKernel (2 * t) z₁ * S₁) *
              (complexExpSecondDifferenceKernel (3 * t) z₂ * S₂) -
            (complexExpSecondDifferenceKernel (2 * t) z₂ * S₂) *
              (complexExpSecondDifferenceKernel (3 * t) z₁ * S₁)) =
      S₁ * (S₂ * S₃) *
        (complexExpSecondDifferenceKernel t z₁ *
            (complexExpSecondDifferenceKernel (2 * t) z₂ *
                complexExpSecondDifferenceKernel (3 * t) z₃ -
              complexExpSecondDifferenceKernel (2 * t) z₃ *
                complexExpSecondDifferenceKernel (3 * t) z₂) -
          complexExpSecondDifferenceKernel t z₂ *
            (complexExpSecondDifferenceKernel (2 * t) z₁ *
                complexExpSecondDifferenceKernel (3 * t) z₃ -
              complexExpSecondDifferenceKernel (2 * t) z₃ *
                complexExpSecondDifferenceKernel (3 * t) z₁) +
          complexExpSecondDifferenceKernel t z₃ *
            (complexExpSecondDifferenceKernel (2 * t) z₁ *
                complexExpSecondDifferenceKernel (3 * t) z₂ -
              complexExpSecondDifferenceKernel (2 * t) z₂ *
                complexExpSecondDifferenceKernel (3 * t) z₁)) := by
    ring_nf
  simp [bareThreeOrbitEvaluationDeterminant, complexExpSecondDifferenceKernel,
    ht, h2, h3] at hdet ⊢
  field_simp [ht] at hdet ⊢

/-! ## C0-D: actual Xi-window nested eventual corollaries -/

/-- On a fixed actual Xi window, the two-orbit Mellin determinant is eventually
nonzero first in the positive box width and then in the punctured finite
dilation parameter. -/
theorem eventually_mellinTwoOrbitEvaluationDeterminant_ne_zero
    {R : ℝ} {z₁ z₂ : ℂ}
    (hz₁ : z₁ ∈ pascalCenteredXiZeroDiskFinset R)
    (hz₂ : z₂ ∈ pascalCenteredXiZeroDiskFinset R)
    (h₁₂ : z₁ ^ 2 ≠ z₂ ^ 2) :
    ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) ({0}ᶜ),
        mellinTwoOrbitEvaluationDeterminant ε t z₁ z₂ ≠ 0 := by
  filter_upwards [eventually_pascalCenteredXiMellinSpectralWeight_ne_zero_on_actual_window R]
    with ε hε
  have hS₁ := hε z₁ hz₁
  have hS₂ := hε z₂ hz₂
  have hbare := eventually_bareTwoOrbitEvaluationDeterminant_ne_zero
    (pascalCenteredXiZeroDiskFinset_sq_ne_zero hz₁)
    (pascalCenteredXiZeroDiskFinset_sq_ne_zero hz₂) h₁₂
  filter_upwards [hbare, self_mem_nhdsWithin] with t hbare htmem
  have ht : t ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using htmem
  rw [mellinTwoOrbitEvaluationDeterminant_eq_spectral_mul_bare ht]
  exact mul_ne_zero (mul_ne_zero hS₁ hS₂) hbare

/-- On a fixed actual Xi window, the three-orbit Mellin determinant is
eventually nonzero with the prescribed nested `ε`-then-`t` quantifiers. -/
theorem eventually_mellinThreeOrbitEvaluationDeterminant_ne_zero
    {R : ℝ} {z₁ z₂ z₃ : ℂ}
    (hz₁ : z₁ ∈ pascalCenteredXiZeroDiskFinset R)
    (hz₂ : z₂ ∈ pascalCenteredXiZeroDiskFinset R)
    (hz₃ : z₃ ∈ pascalCenteredXiZeroDiskFinset R)
    (h₁₂ : z₁ ^ 2 ≠ z₂ ^ 2) (h₁₃ : z₁ ^ 2 ≠ z₃ ^ 2)
    (h₂₃ : z₂ ^ 2 ≠ z₃ ^ 2) :
    ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) ({0}ᶜ),
        mellinThreeOrbitEvaluationDeterminant ε t z₁ z₂ z₃ ≠ 0 := by
  filter_upwards [eventually_pascalCenteredXiMellinSpectralWeight_ne_zero_on_actual_window R]
    with ε hε
  have hS₁ := hε z₁ hz₁
  have hS₂ := hε z₂ hz₂
  have hS₃ := hε z₃ hz₃
  have hbare := eventually_bareThreeOrbitEvaluationDeterminant_ne_zero
    (pascalCenteredXiZeroDiskFinset_sq_ne_zero hz₁)
    (pascalCenteredXiZeroDiskFinset_sq_ne_zero hz₂)
    (pascalCenteredXiZeroDiskFinset_sq_ne_zero hz₃) h₁₂ h₁₃ h₂₃
  filter_upwards [hbare, self_mem_nhdsWithin] with t hbare htmem
  have ht : t ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using htmem
  rw [mellinThreeOrbitEvaluationDeterminant_eq_spectral_mul_bare ht]
  exact mul_ne_zero (mul_ne_zero hS₁ (mul_ne_zero hS₂ hS₃)) hbare

end DkMath.RH.CFBRCProjection
