/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiMellinGeneralFiniteRankAudit
import Mathlib.Tactic

/-!
# General symmetric-numerator Mellin jets

This module exposes the unpatched symmetric exponential numerator and proves
its arbitrary even finite jet.  The numerator is used before division by
`τ ^ 2`, so its value at `τ = 0` is correctly zero and is not confused with
the patched value of the bare kernel.  The finite coefficient matrix is the
one from the general Vandermonde rank audit.

Finite evaluation-point existence and actual Xi-window transfer are
intentionally outside this module.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open Filter

/-- The symmetric exponential numerator before the patched kernel division. -/
noncomputable def mellinSymmetricNumerator (τ : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((τ : ℂ) * z) - 2 + Complex.exp (-(τ : ℂ) * z)

/-- The coefficient of `τ ^ (2*r+2)` in the symmetric numerator. -/
def mellinSymmetricNumeratorJetCoeff (r : ℕ) (z : ℂ) : ℂ :=
  2 * z ^ (2 * r + 2) / (Nat.factorial (2 * r + 2) : ℂ)

/-- The coefficient agrees with the general coefficient matrix after the
substitution `q = z ^ 2`. -/
theorem mellinSymmetricNumeratorJetCoeff_eq_generalCoeff
    (r : ℕ) (z : ℂ) :
    mellinSymmetricNumeratorJetCoeff r z =
      2 * (z ^ 2) ^ (r + 1) / (Nat.factorial (2 * r + 2) : ℂ) := by
  unfold mellinSymmetricNumeratorJetCoeff
  congr 1
  ring

/-- Each numerator jet coefficient is exactly the corresponding entry of the
general squared-coordinate coefficient matrix. -/
theorem mellinSymmetricNumeratorJetCoeff_eq_coefficientMatrix
    {n : ℕ} (z : Fin n → ℂ) (r j : Fin n) :
    mellinSymmetricNumeratorJetCoeff r.1 (z j) =
      mellinJetCoefficientMatrix (fun j => (z j) ^ 2) r j := by
  unfold mellinSymmetricNumeratorJetCoeff mellinJetCoefficientMatrix
  ring_nf

theorem mellinSymmetricNumerator_zero (z : ℂ) :
    mellinSymmetricNumerator 0 z = 0 := by
  norm_num [mellinSymmetricNumerator]

theorem mellinSymmetricNumerator_zero_coordinate (τ : ℝ) :
    mellinSymmetricNumerator τ 0 = 0 := by
  norm_num [mellinSymmetricNumerator]

theorem mellinSymmetricNumerator_neg (τ : ℝ) (z : ℂ) :
    mellinSymmetricNumerator τ (-z) = mellinSymmetricNumerator τ z := by
  unfold mellinSymmetricNumerator
  simp only [mul_neg, neg_mul, neg_neg]
  ring_nf

theorem mellinSymmetricNumerator_eq_kernel_mul
    {τ : ℝ} (hτ : τ ≠ 0) (z : ℂ) :
    mellinSymmetricNumerator τ z = (τ : ℂ) ^ 2 *
      complexExpSecondDifferenceKernel τ z := by
  rw [complexExpSecondDifferenceKernel, if_neg hτ]
  unfold mellinSymmetricNumerator
  field_simp [hτ]

private noncomputable def symmetricExpTaylorRemainder (n : ℕ) (x : ℂ) : ℂ :=
  Complex.exp x - ∑ k ∈ Finset.range (n + 1), x ^ k / (Nat.factorial k : ℂ)

private theorem symmetricExpTaylorRemainder_isLittleO (n : ℕ) :
    (fun x : ℂ => symmetricExpTaylorRemainder n x) =o[nhds 0]
      (fun x : ℂ => x ^ n) := by
  unfold symmetricExpTaylorRemainder
  simpa [Finset.sum_range_succ, Nat.factorial] using
    (Complex.exp_sub_sum_range_succ_isLittleO_pow n)

private theorem symmetricExpTaylorRemainder_scaled_tendsto_zero
    (n : ℕ) (z : ℂ) (sign : ℂ)
    (hsign : sign = 1 ∨ sign = -1) :
    Tendsto
      (fun τ : ℝ =>
        symmetricExpTaylorRemainder n (sign * (τ : ℂ) * z) /
          (τ : ℂ) ^ n)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds 0) := by
  have hremzero : symmetricExpTaylorRemainder n 0 = 0 := by
    have hsum : ∀ m : ℕ,
        ∑ k ∈ Finset.range (m + 1),
          (0 : ℂ) ^ k / (Nat.factorial k : ℂ) = 1 := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => simp [Finset.sum_range_succ, ih]
    simp [symmetricExpTaylorRemainder, hsum]
  by_cases hz : z = 0
  · simp [hz, hremzero]
  have hrem := (symmetricExpTaylorRemainder_isLittleO n).tendsto_div_nhds_zero
  have hτ : Tendsto (fun τ : ℝ => (τ : ℂ))
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hx : Tendsto
      (fun τ : ℝ => sign * (τ : ℂ) * z)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hτ).mul tendsto_const_nhds
  have hcomp := hrem.comp hx
  have hmul := hcomp.mul_const ((sign * z) ^ n)
  have hmul' : Tendsto
      (fun τ : ℝ =>
        symmetricExpTaylorRemainder n (sign * (τ : ℂ) * z) /
          (sign * (τ : ℂ) * z) ^ n * (sign * z) ^ n)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds 0) := by
    simpa [Function.comp_def] using hmul
  apply hmul'.congr'
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  have hτ0 : τ ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hτ
  rcases hsign with rfl | rfl
  · simp only [one_mul]
    field_simp [hτ0, hz]
    ring_nf
  · simp only [neg_one_mul]
    field_simp [hτ0, hz]
    ring

private theorem symmetric_even_sum_identity (m : ℕ) (x : ℂ) :
    ∑ k ∈ Finset.range (2 * m + 3),
        (x ^ k + (-x) ^ k) / (Nat.factorial k : ℂ) =
      ∑ r ∈ Finset.range (m + 2),
        2 * x ^ (2 * r) / (Nat.factorial (2 * r) : ℂ) := by
  induction m with
  | zero =>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  | succ m ih =>
      rw [show 2 * (m + 1) + 3 = (2 * m + 3) + 2 by omega]
      rw [show m + 2 + 1 = (m + 2) + 1 by omega]
      have heven (k : ℕ) : (-x) ^ (2 * k) = x ^ (2 * k) := by
        rw [pow_mul]
        simpa using (pow_mul x 2 k).symm
      have hodd : (-x) ^ (2 * m + 3) = -x ^ (2 * m + 3) := by
        rw [pow_add, heven m]
        ring
      have heven4 : (-x) ^ (2 * m + 4) = x ^ (2 * m + 4) := by
        convert heven (m + 2) using 1 <;> norm_num [Nat.mul_add]
      calc
        (∑ k ∈ Finset.range (2 * m + 3 + 2),
            (x ^ k + (-x) ^ k) / (Nat.factorial k : ℂ)) =
            (∑ k ∈ Finset.range (2 * m + 3),
              (x ^ k + (-x) ^ k) / (Nat.factorial k : ℂ)) +
              (x ^ (2 * m + 3) + (-x) ^ (2 * m + 3)) /
                (Nat.factorial (2 * m + 3) : ℂ) +
              (x ^ (2 * m + 4) + (-x) ^ (2 * m + 4)) /
                (Nat.factorial (2 * m + 4) : ℂ) := by
                rw [Finset.sum_range_succ, Finset.sum_range_succ]
        _ = (∑ r ∈ Finset.range (m + 2),
              2 * x ^ (2 * r) / (Nat.factorial (2 * r) : ℂ)) +
              (x ^ (2 * m + 3) + (-x) ^ (2 * m + 3)) /
                (Nat.factorial (2 * m + 3) : ℂ) +
              (x ^ (2 * m + 4) + (-x) ^ (2 * m + 4)) /
                (Nat.factorial (2 * m + 4) : ℂ) := by rw [ih]
        _ = ∑ r ∈ Finset.range (m + 3),
              2 * x ^ (2 * r) / (Nat.factorial (2 * r) : ℂ) := by
                conv_rhs =>
                  rw [show m + 3 = (m + 2) + 1 by omega,
                    Finset.sum_range_succ]
                rw [hodd, heven4]
                ring_nf

private theorem symmetric_even_sum_shift_identity (m : ℕ) (x : ℂ) :
    ∑ r ∈ Finset.range (m + 2),
        2 * x ^ (2 * r) / (Nat.factorial (2 * r) : ℂ) =
      2 + ∑ r ∈ Finset.range (m + 1),
        2 * x ^ (2 * r + 2) / (Nat.factorial (2 * r + 2) : ℂ) := by
  induction m with
  | zero =>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  | succ m ih =>
      conv_lhs =>
        rw [show m + 1 + 2 = (m + 2) + 1 by omega,
          Finset.sum_range_succ]
      conv_rhs =>
        rw [show m + 1 + 1 = (m + 1) + 1 by omega,
          Finset.sum_range_succ]
      rw [ih]
      have hterm :
          2 * x ^ (2 * (m + 2)) / (Nat.factorial (2 * (m + 2)) : ℂ) =
            2 * x ^ (2 * (m + 1) + 2) /
              (Nat.factorial (2 * (m + 1) + 2) : ℂ) := by
        congr 1
      rw [hterm]
      ring

/-- Arbitrary even finite jet of the symmetric numerator.  The remainder is
taken on the punctured neighborhood because the quotient divides by the
corresponding power of the real parameter. -/
theorem tendsto_mellinSymmetricNumerator_generalJet
    (m : ℕ) (z : ℂ) :
    Tendsto
      (fun τ : ℝ =>
        (mellinSymmetricNumerator τ z -
          ∑ r ∈ Finset.range m,
            mellinSymmetricNumeratorJetCoeff r z * (τ : ℂ) ^ (2 * r + 2)) /
          (τ : ℂ) ^ (2 * m + 2))
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhds (mellinSymmetricNumeratorJetCoeff m z)) := by
  have hplus :=
    symmetricExpTaylorRemainder_scaled_tendsto_zero
      (2 * m + 2) z 1 (Or.inl rfl)
  have hminus :=
    symmetricExpTaylorRemainder_scaled_tendsto_zero
      (2 * m + 2) z (-1) (Or.inr rfl)
  have hsum : Tendsto
      (fun τ : ℝ =>
        mellinSymmetricNumeratorJetCoeff m z +
          symmetricExpTaylorRemainder (2 * m + 2) ((τ : ℂ) * z) /
            (τ : ℂ) ^ (2 * m + 2) +
          symmetricExpTaylorRemainder (2 * m + 2) (-(τ : ℂ) * z) /
            (τ : ℂ) ^ (2 * m + 2))
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhds (mellinSymmetricNumeratorJetCoeff m z)) := by
    simpa using (tendsto_const_nhds.add hplus).add hminus
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  have hτ0 : τ ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hτ
  let x : ℂ := (τ : ℂ) * z
  have hsumid := symmetric_even_sum_identity m x
  have hexp : Complex.exp x =
      symmetricExpTaylorRemainder (2 * m + 2) x +
        ∑ k ∈ Finset.range (2 * m + 3),
          x ^ k / (Nat.factorial k : ℂ) := by
    unfold symmetricExpTaylorRemainder
    ring
  have hexpneg : Complex.exp (-x) =
      symmetricExpTaylorRemainder (2 * m + 2) (-x) +
        ∑ k ∈ Finset.range (2 * m + 3),
          (-x) ^ k / (Nat.factorial k : ℂ) := by
    unfold symmetricExpTaylorRemainder
    ring
  have hsumid' :
      (∑ k ∈ Finset.range (2 * m + 3),
          x ^ k / (Nat.factorial k : ℂ)) +
        ∑ k ∈ Finset.range (2 * m + 3),
          (-x) ^ k / (Nat.factorial k : ℂ) =
      ∑ r ∈ Finset.range (m + 2),
        2 * x ^ (2 * r) / (Nat.factorial (2 * r) : ℂ) := by
    calc
      (∑ k ∈ Finset.range (2 * m + 3),
          x ^ k / (Nat.factorial k : ℂ)) +
          ∑ k ∈ Finset.range (2 * m + 3),
            (-x) ^ k / (Nat.factorial k : ℂ) =
        ∑ k ∈ Finset.range (2 * m + 3),
          (x ^ k + (-x) ^ k) / (Nat.factorial k : ℂ) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro k hk
            ring
      _ = _ := hsumid
  have hG : Complex.exp x - 2 + Complex.exp (-x) =
      symmetricExpTaylorRemainder (2 * m + 2) x +
        symmetricExpTaylorRemainder (2 * m + 2) (-x) - 2 +
          ∑ r ∈ Finset.range (m + 2),
            2 * x ^ (2 * r) / (Nat.factorial (2 * r) : ℂ) := by
    rw [hexp, hexpneg]
    linear_combination hsumid'
  unfold mellinSymmetricNumerator mellinSymmetricNumeratorJetCoeff
  dsimp [x] at hsumid hexp hexpneg hG ⊢
  simp only [neg_mul] at hsumid hexpneg hG ⊢
  rw [hG]
  have hsum_succ := symmetric_even_sum_shift_identity m x
  rw [hsum_succ]
  have hlow :
      ∑ r ∈ Finset.range (m + 1),
          2 * x ^ (2 * r + 2) / (Nat.factorial (2 * r + 2) : ℂ) =
        (∑ r ∈ Finset.range m,
          (2 * z ^ (2 * r + 2) / (Nat.factorial (2 * r + 2) : ℂ)) *
            (τ : ℂ) ^ (2 * r + 2)) +
        2 * z ^ (2 * m + 2) / (Nat.factorial (2 * m + 2) : ℂ) *
          (τ : ℂ) ^ (2 * m + 2) := by
    rw [show m + 1 = m + 1 by rfl, Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro r hr
      dsimp [x]
      field_simp
      ring
    · dsimp [x]
      field_simp
      ring
  rw [hlow]
  field_simp [hτ0]
  ring

end DkMath.RH.CFBRCProjection
