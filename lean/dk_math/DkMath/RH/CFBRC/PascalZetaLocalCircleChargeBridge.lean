/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalZetaZeroMultiplicityBridge
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.PascalZetaLocalCircleChargeBridge"

/-!
# Local circle charges of zeta zeros

This module uses Mathlib's `Complex.circleIntegral` orientation and normalization
as its contour convention.  It sums independent small-circle charges only; it
does not identify that finite sum with an outer contour.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-- A radius whose closed disk avoids the zeta pole and contains no zeta zero
other than its center. -/
def IsPascalZetaIsolatingRadius (ρ : ℂ) (r : ℝ) : Prop :=
  0 < r ∧
    Metric.closedBall ρ r ⊆ ({1}ᶜ : Set ℂ) ∧
    ∀ z ∈ Metric.closedBall ρ r, z ≠ ρ → riemannZeta z ≠ 0

/-- Every zeta zero has a positive isolating radius. -/
theorem exists_isPascalZetaIsolatingRadius
    {ρ : ℂ} (hρ : ρ ∈ riemannZetaZeros) :
    ∃ r : ℝ, IsPascalZetaIsolatingRadius ρ r := by
  obtain ⟨ε, hε, hεzeros⟩ :=
    Metric.exists_closedBall_inter_eq_singleton_of_discrete isDiscrete_riemannZetaZeros hρ
  have hρ1 : ρ ≠ 1 := ne_one_of_mem_riemannZetaZeros hρ
  have hd : 0 < dist ρ 1 := dist_pos.mpr hρ1
  refine ⟨min ε (dist ρ 1 / 2), lt_min hε (half_pos hd), ?_, ?_⟩
  · intro z hz hz1
    have hbad : dist ρ 1 ≤ min ε (dist ρ 1 / 2) := by
      rw [hz1] at hz
      simpa [dist_comm] using hz
    exact (not_le_of_gt (lt_of_le_of_lt (min_le_right _ _) (half_lt_self hd))) hbad
  · intro z hz hzρ hzero
    have hzε : z ∈ Metric.closedBall ρ ε :=
      Metric.mem_closedBall.mpr ((Metric.mem_closedBall.mp hz).trans (min_le_left _ _))
    have hzzero : z ∈ riemannZetaZeros := hzero
    have : z = ρ := by
      have hzinter : z ∈ Metric.closedBall ρ ε ∩ riemannZetaZeros := ⟨hzε, hzzero⟩
      simpa [hεzeros] using hzinter
    exact hzρ this

/-- A chosen isolating radius, with choice hidden behind its specification theorem. -/
noncomputable def pascalZetaIsolatingRadius (ρ : ℂ) : ℝ :=
  by
    classical
    exact if hρ : ρ ∈ riemannZetaZeros then
      Classical.choose (exists_isPascalZetaIsolatingRadius hρ)
    else 1

theorem pascalZetaIsolatingRadius_spec
    {ρ : ℂ} (hρ : ρ ∈ riemannZetaZeros) :
    IsPascalZetaIsolatingRadius ρ (pascalZetaIsolatingRadius ρ) := by
  classical
  simp only [pascalZetaIsolatingRadius, dite_eq_left hρ]
  exact Classical.choose_spec (exists_isPascalZetaIsolatingRadius hρ)

theorem pascalZetaIsolatingRadius_pos
    {ρ : ℂ} (hρ : ρ ∈ riemannZetaZeros) :
    0 < pascalZetaIsolatingRadius ρ :=
  (pascalZetaIsolatingRadius_spec hρ).1

/-- The regular factor multiplying the Cauchy kernel at `ρ`. -/
noncomputable def pascalZetaLocalResidueKernel (ρ w : ℂ) : ℂ :=
  (w - ρ) * pascalZetaNegLogDeriv w

theorem tendsto_pascalZetaLocalResidueKernel
    {ρ : ℂ} (hρ : ρ ∈ riemannZetaZeros) :
    Tendsto (pascalZetaLocalResidueKernel ρ) (𝓝[≠] ρ)
      (𝓝 (-(riemannZetaZeroMultiplicity ρ : ℂ))) :=
  tendsto_mul_pascalZetaNegLogDeriv_zeroMultiplicity hρ

theorem pascalZetaNegLogDeriv_eq_inv_mul_localResidueKernel
    {ρ w : ℂ} (hw : w ≠ ρ) :
    pascalZetaNegLogDeriv w =
      (w - ρ)⁻¹ * pascalZetaLocalResidueKernel ρ w := by
  rw [pascalZetaLocalResidueKernel]
  field_simp

theorem differentiableAt_pascalZetaLocalResidueKernel_of_isolatingRadius
    {ρ z : ℂ} {r : ℝ} (hr : IsPascalZetaIsolatingRadius ρ r)
    (hz : z ∈ Metric.ball ρ r \ {ρ}) :
    DifferentiableAt ℂ (pascalZetaLocalResidueKernel ρ) z := by
  have hzdomain : z ∈ ({1}ᶜ : Set ℂ) := hr.2.1
    (Metric.ball_subset_closedBall hz.1)
  have hzanalytic : AnalyticAt ℂ riemannZeta z := analyticOn_riemannZeta z hzdomain
  have hzne : riemannZeta z ≠ 0 := hr.2.2 z
    (Metric.ball_subset_closedBall hz.1) (by simpa using hz.2)
  change DifferentiableAt ℂ (fun w => (w - ρ) * (-logDeriv riemannZeta w)) z
  exact (differentiableAt_id.sub_const ρ).mul
    ((hzanalytic.deriv.differentiableAt.div hzanalytic.differentiableAt hzne).neg)

theorem continuousOn_pascalZetaLocalResidueKernel_of_isolatingRadius
    {ρ : ℂ} {r : ℝ} (hr : IsPascalZetaIsolatingRadius ρ r) :
    ContinuousOn (pascalZetaLocalResidueKernel ρ) (Metric.closedBall ρ r \ {ρ}) := by
  intro z hz
  have hzdomain : z ∈ ({1}ᶜ : Set ℂ) := hr.2.1 hz.1
  have hzanalytic : AnalyticAt ℂ riemannZeta z := analyticOn_riemannZeta z hzdomain
  have hzne : riemannZeta z ≠ 0 := hr.2.2 z hz.1 (by simpa using hz.2)
  change ContinuousWithinAt (fun w => (w - ρ) * (-logDeriv riemannZeta w))
    (Metric.closedBall ρ r \ {ρ}) z
  exact ((differentiableAt_id.sub_const ρ).mul
    ((hzanalytic.deriv.differentiableAt.div hzanalytic.differentiableAt hzne).neg)).continuousAt.continuousWithinAt

/-- Mathlib's standard oriented local circle charge of `-ζ'/ζ`. -/
theorem circleIntegral_pascalZetaNegLogDeriv_eq_of_isolatingRadius
    {ρ : ℂ} (hρ : ρ ∈ riemannZetaZeros)
    {r : ℝ} (hr : IsPascalZetaIsolatingRadius ρ r) :
    circleIntegral pascalZetaNegLogDeriv ρ r =
      -(2 * Real.pi * Complex.I) * (riemannZetaZeroMultiplicity ρ : ℂ) := by
  have hCauchy :=
    Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto
      (c := ρ) (R := r) hr.1 Set.countable_empty
      (continuousOn_pascalZetaLocalResidueKernel_of_isolatingRadius hr)
      (fun z hz => by
        simpa using differentiableAt_pascalZetaLocalResidueKernel_of_isolatingRadius
          (ρ := ρ) hr ⟨hz.1.1, hz.1.2⟩)
      (tendsto_pascalZetaLocalResidueKernel hρ)
  rw [circleIntegral.integral_congr hr.1.le (fun z hz => ?_)]
  · simpa [smul_eq_mul] using hCauchy
  · have hzρ : z ≠ ρ := by
      intro h
      subst z
      have : (0 : ℝ) = r := by simpa [Metric.mem_sphere] using hz
      exact hr.1.ne' this.symm
    simpa [smul_eq_mul] using
      (pascalZetaNegLogDeriv_eq_inv_mul_localResidueKernel (ρ := ρ) hzρ)

theorem circleIntegral_pascalZetaNegLogDeriv_eq
    {ρ : ℂ} (hρ : ρ ∈ riemannZetaZeros) :
    circleIntegral pascalZetaNegLogDeriv ρ (pascalZetaIsolatingRadius ρ) =
      -(2 * Real.pi * Complex.I) * (riemannZetaZeroMultiplicity ρ : ℂ) :=
  circleIntegral_pascalZetaNegLogDeriv_eq_of_isolatingRadius hρ
    (pascalZetaIsolatingRadius_spec hρ)

/-- The local circle charge divided by Mathlib's `2πi` normalization. -/
noncomputable def pascalZetaNormalizedLocalCircleCharge (ρ : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ *
    circleIntegral pascalZetaNegLogDeriv ρ (pascalZetaIsolatingRadius ρ)

@[simp] theorem pascalZetaNormalizedLocalCircleCharge_eq_neg_multiplicity
    {ρ : ℂ} (hρ : ρ ∈ riemannZetaZeros) :
    pascalZetaNormalizedLocalCircleCharge ρ =
      -(riemannZetaZeroMultiplicity ρ : ℂ) := by
  rw [pascalZetaNormalizedLocalCircleCharge,
    circleIntegral_pascalZetaNegLogDeriv_eq hρ]
  have htwoPiI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
    · exact Complex.I_ne_zero
  field_simp

/-- The sum of independent local circle charges in a finite critical-mirror window.
It is not an outer-contour integral. -/
noncomputable def pascalCriticalMirrorZeroWindowLocalContourMass (R : ℝ) : ℂ :=
  ∑ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
    circleIntegral pascalZetaNegLogDeriv ρ (pascalZetaIsolatingRadius ρ)

theorem pascalCriticalMirrorZeroWindowLocalContourMass_eq
    (R : ℝ) :
    pascalCriticalMirrorZeroWindowLocalContourMass R =
      -(2 * Real.pi * Complex.I) *
        (pascalCriticalMirrorZeroWindowMultiplicity R : ℂ) := by
  classical
  change (∑ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
      circleIntegral pascalZetaNegLogDeriv ρ (pascalZetaIsolatingRadius ρ)) =
    -(2 * Real.pi * Complex.I) *
      ↑(∑ ρ ∈ pascalCriticalMirrorZeroWindowFinset R, riemannZetaZeroMultiplicity ρ)
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hρzero : ρ ∈ riemannZetaZeros :=
    nontrivialRiemannZetaZero_mem_riemannZetaZeros
      ((mem_pascalCriticalMirrorZeroWindowFinset_iff.mp hρ).2)
  rw [circleIntegral_pascalZetaNegLogDeriv_eq hρzero]

theorem pascalCriticalMirrorZeroWindowNormalizedLocalContourMass_eq
    (R : ℝ) :
    (2 * Real.pi * Complex.I)⁻¹ *
      pascalCriticalMirrorZeroWindowLocalContourMass R =
      -(pascalCriticalMirrorZeroWindowMultiplicity R : ℂ) := by
  rw [pascalCriticalMirrorZeroWindowLocalContourMass_eq]
  have htwoPiI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
    · exact Complex.I_ne_zero
  field_simp

end DkMath.RH.CFBRCProjection
