/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiActualWindowVariableWeightRankTransfer
import Mathlib.Tactic

/-!
# Mellin finite-jet rank audit

This module records exact finite asymptotic jets of the zero-independent
exponential symmetric second-difference kernel.  The spectral factor and the
actual Xi carrier are handled only after the bare-kernel coefficients have
been proved.  No Taylor-series heuristic, positivity statement, RH input, or
limit exchange is used.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open Filter

private noncomputable def expTaylorRemainder (n : ℕ) (x : ℂ) : ℂ :=
  Complex.exp x - ∑ k ∈ Finset.range (n + 1), x ^ k / (Nat.factorial k : ℂ)

private theorem expTaylorRemainder_isLittleO (n : ℕ) :
    (fun x : ℂ => expTaylorRemainder n x) =o[nhds 0]
      (fun x : ℂ => x ^ n) := by
  unfold expTaylorRemainder
  simpa [Finset.sum_range_succ, Nat.factorial] using
    (Complex.exp_sub_sum_range_succ_isLittleO_pow n)

private theorem expTaylorRemainder_scaled_tendsto_zero
    (n : ℕ) (z : ℂ) (sign : ℂ)
    (hsign : sign = 1 ∨ sign = -1) :
    Tendsto
      (fun τ : ℝ =>
        expTaylorRemainder n (sign * (τ : ℂ) * z) /
          (τ : ℂ) ^ n)
      (nhds 0) (nhds 0) := by
  have hsum : ∀ m : ℕ,
      ∑ k ∈ Finset.range (m + 1),
        (0 : ℂ) ^ k / (Nat.factorial k : ℂ) = 1 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => simp [Finset.sum_range_succ, ih]
  have hremzero : expTaylorRemainder n 0 = 0 := by
    simp [expTaylorRemainder, hsum]
  by_cases hz : z = 0
  · simp [hz, hremzero]
  have hquot :=
    (expTaylorRemainder_isLittleO n).tendsto_div_nhds_zero
  have hτ : Tendsto (fun τ : ℝ => (τ : ℂ)) (nhds 0) (nhds 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto
  have hx : Tendsto
      (fun τ : ℝ => sign * (τ : ℂ) * z) (nhds 0) (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hτ).mul tendsto_const_nhds
  have hcomp := hquot.comp hx
  have hmul := hcomp.mul_const ((sign * z) ^ n)
  have hmul' : Tendsto
      (fun τ : ℝ =>
        expTaylorRemainder n (sign * (τ : ℂ) * z) /
          (sign * (τ : ℂ) * z) ^ n * (sign * z) ^ n)
      (nhds 0) (nhds 0) := by
    simpa [Function.comp_def] using hmul
  apply hmul'.congr'
  filter_upwards [] with τ
  rcases hsign with rfl | rfl
  · by_cases hτ0 : τ = 0
    · simp [hτ0, hremzero]
    · simp only [one_mul]
      field_simp [hτ0, hz]
      ring_nf
  · by_cases hτ0 : τ = 0
    · simp [hτ0, hremzero]
    · simp only [neg_one_mul]
      field_simp [hτ0, hz]
      ring_nf

/-- The quadratic coefficient of the pure symmetric exponential kernel is
`z ^ 2`, with the quotient at `τ = 0` interpreted by the existing patch. -/
theorem tendsto_complexExpSecondDifferenceKernel_quadraticJet
    (z : ℂ) :
    Tendsto
      (fun τ : ℝ => complexExpSecondDifferenceKernel τ z)
      (nhds 0) (nhds (z ^ 2)) :=
  tendsto_complexExpSecondDifferenceKernel_zero z

/-! The next jet statements use the punctured neighborhood at zero.  This
avoids confusing the patched value of the kernel at `τ = 0` with a quotient
whose denominator has been formally divided by zero. -/

/-- The second even jet of the bare Mellin kernel is `z ^ 4 / 12`. -/
theorem tendsto_complexExpSecondDifferenceKernel_quarticJet
    (z : ℂ) :
    Tendsto
      (fun τ : ℝ =>
        (complexExpSecondDifferenceKernel τ z - z ^ 2) /
          (τ : ℂ) ^ 2)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (z ^ 4 / 12)) := by
  have hplus :=
    (expTaylorRemainder_scaled_tendsto_zero 4 z 1 (Or.inl rfl)).mono_left
      (nhdsWithin_le_nhds :
        nhdsWithin (0 : ℝ) ({0}ᶜ) ≤ nhds 0)
  have hminus :=
    (expTaylorRemainder_scaled_tendsto_zero 4 z (-1) (Or.inr rfl)).mono_left
      (nhdsWithin_le_nhds :
        nhdsWithin (0 : ℝ) ({0}ᶜ) ≤ nhds 0)
  have hsum : Tendsto
      (fun τ : ℝ => z ^ 4 / 12 +
        expTaylorRemainder 4 ((τ : ℂ) * z) / (τ : ℂ) ^ 4 +
        expTaylorRemainder 4 (-(τ : ℂ) * z) / (τ : ℂ) ^ 4)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (z ^ 4 / 12)) := by
    simpa using (tendsto_const_nhds.add hplus).add hminus
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  have hτ0 : τ ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hτ
  rw [complexExpSecondDifferenceKernel, if_neg hτ0]
  unfold expTaylorRemainder
  field_simp [hτ0]
  norm_num [Finset.sum_range_succ, Nat.factorial]
  ring_nf

/-- The fourth even jet of the bare Mellin kernel is `z ^ 6 / 360`. -/
theorem tendsto_complexExpSecondDifferenceKernel_sexticJet
    (z : ℂ) :
    Tendsto
      (fun τ : ℝ =>
        (complexExpSecondDifferenceKernel τ z - z ^ 2 -
          (τ : ℂ) ^ 2 * (z ^ 4 / 12)) /
          (τ : ℂ) ^ 4)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (z ^ 6 / 360)) := by
  have hplus :=
    (expTaylorRemainder_scaled_tendsto_zero 6 z 1 (Or.inl rfl)).mono_left
      (nhdsWithin_le_nhds :
        nhdsWithin (0 : ℝ) ({0}ᶜ) ≤ nhds 0)
  have hminus :=
    (expTaylorRemainder_scaled_tendsto_zero 6 z (-1) (Or.inr rfl)).mono_left
      (nhdsWithin_le_nhds :
        nhdsWithin (0 : ℝ) ({0}ᶜ) ≤ nhds 0)
  have hsum : Tendsto
      (fun τ : ℝ => z ^ 6 / 360 +
        expTaylorRemainder 6 ((τ : ℂ) * z) / (τ : ℂ) ^ 6 +
        expTaylorRemainder 6 (-(τ : ℂ) * z) / (τ : ℂ) ^ 6)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (z ^ 6 / 360)) := by
    simpa using (tendsto_const_nhds.add hplus).add hminus
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  have hτ0 : τ ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hτ
  rw [complexExpSecondDifferenceKernel, if_neg hτ0]
  unfold expTaylorRemainder
  field_simp [hτ0]
  norm_num [Finset.sum_range_succ, Nat.factorial]
  ring_nf

/-! ## Gate B obstruction: the zero squared-coordinate is invisible -/

/-- The bare symmetric exponential kernel has no response at the coordinate
`z = 0`, for any dilation parameter, including the patched value at `τ = 0`.
This is the exact obstruction that prevents an unconditional orbit-rank
statement from silently absorbing a possible zero squared-coordinate. -/
theorem complexExpSecondDifferenceKernel_zero_coordinate (τ : ℝ) :
    complexExpSecondDifferenceKernel τ 0 = 0 := by
  by_cases hτ : τ = 0
  · norm_num [complexExpSecondDifferenceKernel, hτ]
  · norm_num [complexExpSecondDifferenceKernel, hτ]

/-- The actual centered Mellin family also vanishes at `z = 0`.  Consequently
the two-orbit rank step requires an independently proved exclusion of the
zero coordinate before it can be promoted to a statement about the actual
Xi window. -/
theorem pascalCenteredXiMellinSecondDifferenceWeight_zero_coordinate
    {ε : ℝ} (hε : 0 < ε) (τ : ℝ) :
    pascalCenteredXiMellinSecondDifferenceWeight ε τ 0 = 0 := by
  by_cases hτ : τ = 0
  · subst τ
    rw [pascalCenteredXiMellinSecondDifferenceWeight_tau_zero_eq_quadraticWeight
      hε]
    simp
  · rw [pascalCenteredXiMellinSecondDifferenceWeight_eq_kernel_mul hτ]
    norm_num [hτ]

end DkMath.RH.CFBRCProjection
