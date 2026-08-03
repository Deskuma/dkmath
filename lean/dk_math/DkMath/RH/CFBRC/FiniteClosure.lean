/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.OffCriticalExclusionGeneral
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.FiniteClosure"

namespace DkMath.RH.CFBRCProjection

/-- Endpoint of a finite complex-vector family. -/
noncomputable def finiteEndpoint
    {ι : Type*} (S : Finset ι) (v : ι → ℂ) : ℂ :=
  S.sum v

/-- Endpoint after applying one common complex rotation/multiplier. -/
noncomputable def rotatedFiniteEndpoint
    {ι : Type*} (S : Finset ι) (v : ι → ℂ) (ω : ℂ) : ℂ :=
  ω * finiteEndpoint S v

/-- Positive real-axis mass after the common rotation. -/
noncomputable def positiveProjectedMass
    {ι : Type*} (S : Finset ι) (v : ι → ℂ) (ω : ℂ) : ℝ :=
  S.sum fun i => max (ω * v i).re 0

/-- Absolute negative real-axis mass after the common rotation. -/
noncomputable def negativeProjectedMass
    {ι : Type*} (S : Finset ι) (v : ι → ℂ) (ω : ℂ) : ℝ :=
  S.sum fun i => max (-(ω * v i).re) 0

/-- Imaginary residual of the rotated endpoint. -/
noncomputable def transverseGap
    {ι : Type*} (S : Finset ι) (v : ι → ℂ) (ω : ℂ) : ℝ :=
  (rotatedFiniteEndpoint S v ω).im

/-- Positive part minus negative part reconstructs a real scalar. -/
theorem max_sub_max_neg_eq_self (x : ℝ) :
    max x 0 - max (-x) 0 = x := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
    ring
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [max_eq_right hx', max_eq_left (neg_nonneg.mpr hx')]
    ring

/-- The rotated endpoint is the sum of the individually rotated vectors. -/
theorem rotatedFiniteEndpoint_eq_sum
    {ι : Type*} (S : Finset ι) (v : ι → ℂ) (ω : ℂ) :
    rotatedFiniteEndpoint S v ω = S.sum (fun i => ω * v i) := by
  unfold rotatedFiniteEndpoint finiteEndpoint
  rw [Finset.mul_sum]

/-- The real endpoint is positive projected mass minus negative projected mass. -/
theorem rotatedFiniteEndpoint_re_eq_mass_sub
    {ι : Type*} (S : Finset ι) (v : ι → ℂ) (ω : ℂ) :
    (rotatedFiniteEndpoint S v ω).re =
      positiveProjectedMass S v ω - negativeProjectedMass S v ω := by
  calc
    (rotatedFiniteEndpoint S v ω).re =
        S.sum (fun i => (ω * v i).re) := by
      rw [rotatedFiniteEndpoint_eq_sum]
      simp
    _ = S.sum (fun i =>
        max (ω * v i).re 0 - max (-(ω * v i).re) 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (max_sub_max_neg_eq_self (ω * v i).re).symm
    _ = positiveProjectedMass S v ω - negativeProjectedMass S v ω := by
      rw [positiveProjectedMass, negativeProjectedMass,
        Finset.sum_sub_distrib]

/-- A nonzero common rotation preserves finite closure. -/
theorem rotatedFiniteEndpoint_eq_zero_iff
    {ι : Type*} (S : Finset ι) (v : ι → ℂ) {ω : ℂ}
    (hω : ω ≠ 0) :
    rotatedFiniteEndpoint S v ω = 0 ↔ finiteEndpoint S v = 0 := by
  simp [rotatedFiniteEndpoint, hω]

/--
Finite complex closure is exactly projected mass balance together with zero
transverse gap.
-/
theorem rotatedFiniteEndpoint_eq_zero_iff_mass_balance_and_transverseGap
    {ι : Type*} (S : Finset ι) (v : ι → ℂ) (ω : ℂ) :
    rotatedFiniteEndpoint S v ω = 0 ↔
      positiveProjectedMass S v ω = negativeProjectedMass S v ω ∧
      transverseGap S v ω = 0 := by
  constructor
  · intro hzero
    constructor
    · have hre : (rotatedFiniteEndpoint S v ω).re = 0 := by
        rw [hzero]
        simp
      rw [rotatedFiniteEndpoint_re_eq_mass_sub] at hre
      linarith
    · simp [transverseGap, hzero]
  · rintro ⟨hbalance, hgap⟩
    apply Complex.ext
    · simp only [Complex.zero_re]
      rw [rotatedFiniteEndpoint_re_eq_mass_sub]
      exact sub_eq_zero.mpr hbalance
    · simpa [transverseGap] using hgap

/--
For a nonzero rotation, unrotated closure is equivalent to mass balance and
zero transverse gap in the rotated coordinate system.
-/
theorem finiteEndpoint_eq_zero_iff_mass_balance_and_transverseGap
    {ι : Type*} (S : Finset ι) (v : ι → ℂ) {ω : ℂ}
    (hω : ω ≠ 0) :
    finiteEndpoint S v = 0 ↔
      positiveProjectedMass S v ω = negativeProjectedMass S v ω ∧
      transverseGap S v ω = 0 := by
  rw [← rotatedFiniteEndpoint_eq_zero_iff S v hω]
  exact rotatedFiniteEndpoint_eq_zero_iff_mass_balance_and_transverseGap S v ω

end DkMath.RH.CFBRCProjection
