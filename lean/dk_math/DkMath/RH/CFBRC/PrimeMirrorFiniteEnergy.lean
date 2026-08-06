/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PrimeMirrorOffsetCore
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.PrimeMirrorFiniteEnergy"

/-!
# Finite prime-mirror energy

This module lifts the one-mode mirror-offset Gap to a finite coordinate energy.
It deliberately keeps the coordinate set and weight function abstract.  A later
Pascal or Euler bridge may supply the concrete finite prime set and weights.

The energy is a sum of coordinate norm-squares, not the norm-square of one
complex sum.  This distinction prevents cancellation between different prime
modes from erasing the horizontal offset information.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

/-- Finite weighted sum of mirror-offset Gaps. -/
noncomputable def primeMirrorEnergy
    (S : Finset ℕ) (weight : ℕ → ℝ) (δ : ℝ) : ℝ :=
  ∑ n ∈ S, weight n * primeMirrorOffsetGap n δ

/-- Finite weighted mirror energy evaluated at the centered coordinate of `s`. -/
noncomputable def primeMirrorEnergyAt
    (S : Finset ℕ) (weight : ℕ → ℝ) (s : ℂ) : ℝ :=
  primeMirrorEnergy S weight (centeredSigma s.re)

/-- Cutoff form of the finite energy, using the modes in `Finset.range N`. -/
noncomputable def primeMirrorEnergyUpTo
    (weight : ℕ → ℝ) (N : ℕ) (δ : ℝ) : ℝ :=
  primeMirrorEnergy (Finset.range N) weight δ

/-- Every finite mirror energy with nonnegative weights is nonnegative. -/
theorem primeMirrorEnergy_nonneg
    {S : Finset ℕ} {weight : ℕ → ℝ}
    (hweight : ∀ n ∈ S, 0 ≤ weight n)
    (δ : ℝ) :
    0 ≤ primeMirrorEnergy S weight δ := by
  unfold primeMirrorEnergy
  exact Finset.sum_nonneg fun n hn =>
    mul_nonneg
      (hweight n hn)
      (primeMirrorOffsetGap_nonneg n δ)

/-- One selected mode is a lower bound for the full nonnegative finite energy. -/
theorem primeMirrorEnergy_mode_le
    {S : Finset ℕ} {weight : ℕ → ℝ} {p : ℕ}
    (hpS : p ∈ S)
    (hweight : ∀ n ∈ S, 0 ≤ weight n)
    (δ : ℝ) :
    weight p * primeMirrorOffsetGap p δ ≤
      primeMirrorEnergy S weight δ := by
  unfold primeMirrorEnergy
  exact Finset.single_le_sum
    (s := S)
    (f := fun n : ℕ => weight n * primeMirrorOffsetGap n δ)
    (fun n hn =>
      mul_nonneg
        (hweight n hn)
        (primeMirrorOffsetGap_nonneg n δ))
    hpS

/--
A finite energy is strictly positive off center when it contains one
nonconstant mode with positive weight and all remaining weights are nonnegative.
-/
theorem primeMirrorEnergy_pos_of_mode
    {S : Finset ℕ} {weight : ℕ → ℝ} {p : ℕ} {δ : ℝ}
    (hpS : p ∈ S)
    (hpMode : 1 < p)
    (hpWeight : 0 < weight p)
    (hweight : ∀ n ∈ S, 0 ≤ weight n)
    (hδ : δ ≠ 0) :
    0 < primeMirrorEnergy S weight δ := by
  have hterm :
      0 < weight p * primeMirrorOffsetGap p δ :=
    mul_pos hpWeight
      (primeMirrorOffsetGap_pos_of_delta_ne_zero hpMode hδ)
  have hle :
      weight p * primeMirrorOffsetGap p δ ≤
        primeMirrorEnergy S weight δ :=
    primeMirrorEnergy_mode_le hpS hweight δ
  exact lt_of_lt_of_le hterm hle

/--
With a nonempty collection of nonconstant modes and positive weights, the
finite energy vanishes exactly at zero horizontal offset.
-/
theorem primeMirrorEnergy_eq_zero_iff_delta_eq_zero
    {S : Finset ℕ} {weight : ℕ → ℝ}
    (hS : S.Nonempty)
    (hmode : ∀ n ∈ S, 1 < n)
    (hweight : ∀ n ∈ S, 0 < weight n)
    (δ : ℝ) :
    primeMirrorEnergy S weight δ = 0 ↔ δ = 0 := by
  constructor
  · intro henergy
    by_contra hδ
    rcases hS with ⟨p, hpS⟩
    have hpositive : 0 < primeMirrorEnergy S weight δ :=
      primeMirrorEnergy_pos_of_mode
        hpS
        (hmode p hpS)
        (hweight p hpS)
        (fun n hn => le_of_lt (hweight n hn))
        hδ
    linarith
  · intro hδ
    subst δ
    unfold primeMirrorEnergy
    simp [primeMirrorOffsetGap, primeMirrorLeftAmplitude,
      primeMirrorRightAmplitude]

/-- The finite energy at a complex point vanishes exactly on the critical line. -/
theorem primeMirrorEnergyAt_eq_zero_iff_re_eq_half
    {S : Finset ℕ} {weight : ℕ → ℝ}
    (hS : S.Nonempty)
    (hmode : ∀ n ∈ S, 1 < n)
    (hweight : ∀ n ∈ S, 0 < weight n)
    (s : ℂ) :
    primeMirrorEnergyAt S weight s = 0 ↔
      s.re = (1 : ℝ) / 2 := by
  rw [primeMirrorEnergyAt,
    primeMirrorEnergy_eq_zero_iff_delta_eq_zero hS hmode hweight,
    centeredSigma_eq_zero_iff]

/-- Off the critical line, every admissible finite mirror energy is positive. -/
theorem primeMirrorEnergyAt_pos_of_re_ne_half
    {S : Finset ℕ} {weight : ℕ → ℝ}
    (hS : S.Nonempty)
    (hmode : ∀ n ∈ S, 1 < n)
    (hweight : ∀ n ∈ S, 0 < weight n)
    {s : ℂ}
    (hre : s.re ≠ (1 : ℝ) / 2) :
    0 < primeMirrorEnergyAt S weight s := by
  rcases hS with ⟨p, hpS⟩
  apply primeMirrorEnergy_pos_of_mode
    hpS
    (hmode p hpS)
    (hweight p hpS)
    (fun n hn => le_of_lt (hweight n hn))
  intro hcenter
  exact hre ((centeredSigma_eq_zero_iff s.re).mp hcenter)

/--
The `(N, N+1)` energy-window increment recovers exactly the newly appended
mode energy.
-/
@[simp]
theorem primeMirrorEnergyUpTo_succ_sub
    (weight : ℕ → ℝ) (N : ℕ) (δ : ℝ) :
    primeMirrorEnergyUpTo weight (N + 1) δ -
        primeMirrorEnergyUpTo weight N δ =
      weight N * primeMirrorOffsetGap N δ := by
  simp [primeMirrorEnergyUpTo, primeMirrorEnergy,
    Finset.sum_range_succ]

/-- Consecutive cutoff energies determine the newly appended mode exactly. -/
@[simp]
theorem primeMirrorEnergyUpTo_succ_eq
    (weight : ℕ → ℝ) (N : ℕ) (δ : ℝ) :
    primeMirrorEnergyUpTo weight (N + 1) δ =
      primeMirrorEnergyUpTo weight N δ +
        weight N * primeMirrorOffsetGap N δ := by
  simp [primeMirrorEnergyUpTo, primeMirrorEnergy,
    Finset.sum_range_succ]

end DkMath.RH.CFBRCProjection
