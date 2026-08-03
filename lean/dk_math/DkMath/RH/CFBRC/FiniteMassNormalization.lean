/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.FiniteClosurePermutation
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.FiniteMassNormalization"

namespace DkMath.RH.CFBRCProjection

/-- Total absolute real-axis projected mass. -/
noncomputable def projectedMassTotal
    {ι : Type*} (S : Finset ι) (v : ι → ℂ) (ω : ℂ) : ℝ :=
  positiveProjectedMass S v ω + negativeProjectedMass S v ω

/-- Positive projected mass normalized by the total projected mass. -/
noncomputable def normalizedPositiveProjectedMass
    {ι : Type*} (S : Finset ι) (v : ι → ℂ) (ω : ℂ) : ℝ :=
  positiveProjectedMass S v ω / projectedMassTotal S v ω

/-- Negative projected mass normalized by the total projected mass. -/
noncomputable def normalizedNegativeProjectedMass
    {ι : Type*} (S : Finset ι) (v : ι → ℂ) (ω : ℂ) : ℝ :=
  negativeProjectedMass S v ω / projectedMassTotal S v ω

/-- Normalized left-right center offset. -/
noncomputable def normalizedProjectedCenterOffset
    {ι : Type*} (S : Finset ι) (v : ι → ℂ) (ω : ℂ) : ℝ :=
  normalizedPositiveProjectedMass S v ω -
    normalizedNegativeProjectedMass S v ω

/-- CFBRC Big reconstructed from the two normalized projected masses. -/
noncomputable def normalizedProjectedBig
    {ι : Type*} (S : Finset ι) (v : ι → ℂ) (ω : ℂ) : ℝ :=
  (normalizedPositiveProjectedMass S v ω +
      normalizedNegativeProjectedMass S v ω) ^ 2

/-- Two nontrivially normalized real masses always sum to one. -/
theorem normalized_pair_sum_eq_one
    {a b : ℝ} (hTotal : a + b ≠ 0) :
    a / (a + b) + b / (a + b) = 1 := by
  field_simp [hTotal]

/-- Equal nontrivially normalized masses both become one half. -/
theorem normalized_pair_eq_half_of_eq
    {a b : ℝ} (hab : a = b) (hTotal : a + b ≠ 0) :
    a / (a + b) = (1 : ℝ) / 2 ∧
      b / (a + b) = (1 : ℝ) / 2 := by
  subst b
  have ha : a ≠ 0 := by
    intro ha
    apply hTotal
    simp [ha]
  constructor <;> field_simp [ha] <;> ring

/-- The two normalized finite projected masses sum to one. -/
theorem normalizedProjectedMass_sum_eq_one
    {ι : Type*} (S : Finset ι) (v : ι → ℂ) (ω : ℂ)
    (hTotal : projectedMassTotal S v ω ≠ 0) :
    normalizedPositiveProjectedMass S v ω +
      normalizedNegativeProjectedMass S v ω = 1 := by
  exact normalized_pair_sum_eq_one hTotal

/-- The normalized CFBRC Big is identically one whenever normalization is defined. -/
theorem normalizedProjectedBig_eq_one
    {ι : Type*} (S : Finset ι) (v : ι → ℂ) (ω : ℂ)
    (hTotal : projectedMassTotal S v ω ≠ 0) :
    normalizedProjectedBig S v ω = 1 := by
  rw [normalizedProjectedBig, normalizedProjectedMass_sum_eq_one S v ω hTotal]
  norm_num

/-- Projected mass balance gives the normalized center `1/2, 1/2`. -/
theorem normalizedProjectedMass_eq_half_of_balance
    {ι : Type*} (S : Finset ι) (v : ι → ℂ) (ω : ℂ)
    (hBalance :
      positiveProjectedMass S v ω = negativeProjectedMass S v ω)
    (hTotal : projectedMassTotal S v ω ≠ 0) :
    normalizedPositiveProjectedMass S v ω = (1 : ℝ) / 2 ∧
      normalizedNegativeProjectedMass S v ω = (1 : ℝ) / 2 := by
  exact normalized_pair_eq_half_of_eq hBalance hTotal

/-- Projected mass balance makes the normalized center offset vanish. -/
theorem normalizedProjectedCenterOffset_eq_zero_of_balance
    {ι : Type*} (S : Finset ι) (v : ι → ℂ) (ω : ℂ)
    (hBalance :
      positiveProjectedMass S v ω = negativeProjectedMass S v ω)
    (hTotal : projectedMassTotal S v ω ≠ 0) :
    normalizedProjectedCenterOffset S v ω = 0 := by
  rcases normalizedProjectedMass_eq_half_of_balance S v ω hBalance hTotal with
    ⟨hpos, hneg⟩
  rw [normalizedProjectedCenterOffset, hpos, hneg, sub_self]

/--
A genuine finite closure, observed through a nonzero rotation and a nonzero
projected total mass, has normalized CFBRC coordinates `1/2, 1/2`.
-/
theorem normalizedProjectedMass_eq_half_of_finiteEndpoint_eq_zero
    {ι : Type*} (S : Finset ι) (v : ι → ℂ) {ω : ℂ}
    (hω : ω ≠ 0)
    (hClose : finiteEndpoint S v = 0)
    (hTotal : projectedMassTotal S v ω ≠ 0) :
    normalizedPositiveProjectedMass S v ω = (1 : ℝ) / 2 ∧
      normalizedNegativeProjectedMass S v ω = (1 : ℝ) / 2 := by
  have hBalance :=
    ((finiteEndpoint_eq_zero_iff_mass_balance_and_transverseGap
      S v hω).mp hClose).1
  exact normalizedProjectedMass_eq_half_of_balance S v ω hBalance hTotal

/-- A genuine finite closure passes through normalized center offset zero. -/
theorem normalizedProjectedCenterOffset_eq_zero_of_finiteEndpoint_eq_zero
    {ι : Type*} (S : Finset ι) (v : ι → ℂ) {ω : ℂ}
    (hω : ω ≠ 0)
    (hClose : finiteEndpoint S v = 0)
    (hTotal : projectedMassTotal S v ω ≠ 0) :
    normalizedProjectedCenterOffset S v ω = 0 := by
  have hBalance :=
    ((finiteEndpoint_eq_zero_iff_mass_balance_and_transverseGap
      S v hω).mp hClose).1
  exact normalizedProjectedCenterOffset_eq_zero_of_balance S v ω hBalance hTotal

end DkMath.RH.CFBRCProjection
