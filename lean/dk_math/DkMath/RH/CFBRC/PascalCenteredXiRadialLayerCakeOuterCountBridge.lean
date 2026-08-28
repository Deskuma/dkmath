/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiOuterContourResidueBridge
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.PascalCenteredXiRadialLayerCakeOuterCountBridge"

/-!
# Centered Xi radial layer-cake and fixed outer counts

This module rewrites the non-holomorphic radial second moment as a finite
layer-cake integral of fixed centered-Xi outer multiplicity counts.  The
quantity `Complex.normSq z` remains radial; it is never presented as a
holomorphic contour weight.  Outer-count identities are used pointwise only
at boundary-safe radii and almost everywhere on bounded radius intervals.

The module deliberately proves a representation identity only.  It does not
prove positivity, vanishing of a second-moment defect, horizontal-energy
vanishing, or RH.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open MeasureTheory
open Set
open scoped Topology Interval

/-! ## Phase A: intrinsic radial moment -/

/-- The multiplicity-weighted radial second moment of centered Xi zeros in a disk. -/
noncomputable def pascalCenteredXiZeroDiskRadialSecondMoment (R : ℝ) : ℝ :=
  ∑ z ∈ pascalCenteredXiZeroDiskFinset R,
    (pascalCenteredXiZeroMultiplicity z : ℝ) * Complex.normSq z

/-- The Xi intrinsic radial moment is exactly the transported PPW window moment. -/
@[simp] theorem pascalCenteredXiZeroDiskRadialSecondMoment_eq_window (R : ℝ) :
    pascalCenteredXiZeroDiskRadialSecondMoment R =
      pascalCriticalMirrorZeroWindowRadialSecondMoment R := by
  classical
  rw [pascalCenteredXiZeroDiskRadialSecondMoment,
    ← image_pascalCenterZeroShift_window_eq_centeredXiDisk R]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro s hs
    change (pascalCenteredXiZeroMultiplicity (s - criticalLineCenter) : ℝ) *
        Complex.normSq (s - criticalLineCenter) = _
    rw [pascalCenteredXiZeroMultiplicity_sub_center_eq_riemannZetaZeroMultiplicity
      ((mem_pascalCriticalMirrorZeroWindowFinset_iff.mp hs).2)]
  · intro s hs t ht hst
    have h := congrArg pascalUncenterZeroShift hst
    simpa using h

/-! ## Phase B: finite layer count -/

/-- Multiplicity in the fixed outer disk whose zero radius is at most `r`. -/
noncomputable def pascalCenteredXiZeroDiskLayerCount (R r : ℝ) : ℝ :=
  ∑ z ∈ pascalCenteredXiZeroDiskFinset R,
    if dist z 0 ≤ r then (pascalCenteredXiZeroMultiplicity z : ℝ) else 0

/-- On `0 ≤ r ≤ R`, the fixed-`R` layer count is the intrinsic disk count at `r`. -/
theorem pascalCenteredXiZeroDiskLayerCount_eq_multiplicity
    {R r : ℝ} (_hr0 : 0 ≤ r) (hrR : r ≤ R) :
    pascalCenteredXiZeroDiskLayerCount R r =
      (pascalCenteredXiZeroDiskMultiplicity r : ℝ) := by
  classical
  have hfilter :
      (pascalCenteredXiZeroDiskFinset R).filter (fun z => dist z 0 ≤ r) =
        pascalCenteredXiZeroDiskFinset r := by
    ext z
    simp only [Finset.mem_filter, mem_pascalCenteredXiZeroDiskFinset_iff,
      mem_pascalCenteredXiZeroDisk_iff, and_assoc]
    constructor
    · rintro ⟨hzR, hzero, hzr⟩
      exact ⟨Metric.mem_closedBall.mpr hzr, hzero⟩
    · rintro ⟨hzr, hzero⟩
      exact ⟨Metric.mem_closedBall.mpr (hzr.trans hrR), hzero, hzr⟩
  rw [pascalCenteredXiZeroDiskLayerCount, ← Finset.sum_filter]
  rw [hfilter]
  simp [pascalCenteredXiZeroDiskMultiplicity]

/-- The finite layer count is nonnegative because all multiplicities are nonnegative. -/
theorem pascalCenteredXiZeroDiskLayerCount_nonneg (R r : ℝ) :
    0 ≤ pascalCenteredXiZeroDiskLayerCount R r := by
  classical
  unfold pascalCenteredXiZeroDiskLayerCount
  exact Finset.sum_nonneg fun z hz => by split_ifs <;> positivity

/-- The layer count is monotone in the radius. -/
theorem pascalCenteredXiZeroDiskLayerCount_mono
    (R : ℝ) : Monotone (pascalCenteredXiZeroDiskLayerCount R) := by
  intro r s hrs
  classical
  unfold pascalCenteredXiZeroDiskLayerCount
  apply Finset.sum_le_sum
  intro z hz
  simp only [dist_eq_norm]
  by_cases hzR : ‖z‖ ≤ r
  · simp [hzR, hzR.trans hrs]
  · by_cases hzS : ‖z‖ ≤ s
    · simp [hzR, hzS]
    · simp [hzR, hzS]

/-! ## Phase C: one-zero layer integral -/

/-- The one-zero layer indicator is interval integrable on a nonnegative disk radius. -/
theorem intervalIntegrable_two_mul_radius_indicator_ge_dist
    {R : ℝ} (_hR : 0 ≤ R) {z : ℂ}
    (hz : z ∈ pascalCenteredXiZeroDiskFinset R) :
    IntervalIntegrable
      (fun r => 2 * r * (if dist z 0 ≤ r then (1 : ℝ) else 0)) volume 0 R := by
  let d : ℝ := dist z 0
  let f : ℝ → ℝ := fun r => 2 * r
  let g : ℝ → ℝ := Set.indicator {r : ℝ | r ≤ d} f
  have hd0 : 0 ≤ d := dist_nonneg
  have hdR : d ≤ R := by
    have hzR := (mem_pascalCenteredXiZeroDiskFinset_iff.mp hz).1
    exact Metric.mem_closedBall.mp hzR
  have hf : IntervalIntegrable f volume 0 R := by
    exact (continuous_const.mul continuous_id).intervalIntegrable 0 R
  have hg : IntervalIntegrable g volume 0 R := by
    refine ⟨?_, ?_⟩
    · exact hf.1.indicator measurableSet_Iic
    · exact hf.2.indicator measurableSet_Iic
  have hae :
      (fun r => 2 * r * (if d ≤ r then (1 : ℝ) else 0)) =ᵐ[
        volume.restrict (uIoc 0 R)]
        (fun r => f r - g r) := by
    filter_upwards [ae_restrict_of_ae (Measure.ae_ne volume d)] with r hr
    by_cases hdr : d ≤ r
    · have hrd : ¬r ≤ d := by
        intro hrd
        exact hr (le_antisymm hrd hdr)
      simp [f, g, hdr, hrd]
    · have hrd : r ≤ d := le_of_not_ge hdr
      simp [f, g, hdr, hrd]
  have hdiff : IntervalIntegrable (fun r => f r - g r) volume 0 R :=
    hf.sub hg
  have hdiff' := hdiff.congr_ae hae.symm
  simpa [d] using hdiff'

/-- The one-zero layer-cake integral contributes `R² - |z|²`. -/
theorem intervalIntegral_two_mul_radius_indicator_ge_dist
    {R : ℝ} (hR : 0 ≤ R) {z : ℂ}
    (hz : z ∈ pascalCenteredXiZeroDiskFinset R) :
    (∫ r in 0..R,
      2 * r * (if dist z 0 ≤ r then (1 : ℝ) else 0)) =
      R ^ 2 - (dist z 0) ^ 2 := by
  let d : ℝ := dist z 0
  let f : ℝ → ℝ := fun r => 2 * r
  let g : ℝ → ℝ := Set.indicator {r : ℝ | r ≤ d} f
  have hd0 : 0 ≤ d := by
    exact dist_nonneg
  have hdR : d ≤ R := by
    have hzR := (mem_pascalCenteredXiZeroDiskFinset_iff.mp hz).1
    exact Metric.mem_closedBall.mp hzR
  have hf : IntervalIntegrable f volume 0 R := by
    exact (continuous_const.mul continuous_id).intervalIntegrable 0 R
  have hg : IntervalIntegrable g volume 0 R := by
    refine ⟨?_, ?_⟩
    · exact hf.1.indicator measurableSet_Iic
    · exact hf.2.indicator measurableSet_Iic
  have hae :
      (fun r => 2 * r * (if d ≤ r then (1 : ℝ) else 0)) =ᵐ[
        volume.restrict (uIoc 0 R)]
        (fun r => f r - g r) := by
    filter_upwards [ae_restrict_of_ae (Measure.ae_ne volume d)] with r hr
    by_cases hdr : d ≤ r
    · have hrd : ¬r ≤ d := by
        intro hrd
        exact hr (le_antisymm hrd hdr)
      simp [f, g, hdr, hrd]
    · have hrd : r ≤ d := le_of_not_ge hdr
      simp [f, g, hdr, hrd]
  change (∫ r in 0..R,
      2 * r * (if d ≤ r then (1 : ℝ) else 0)) = _
  have hae' := (ae_restrict_iff' measurableSet_uIoc).mp hae
  have hae'' : ∀ᵐ r ∂volume, r ∈ Ioc 0 R →
      (2 * r * (if d ≤ r then (1 : ℝ) else 0)) = f r - g r := by
    simpa [uIoc_of_le hR] using hae'
  rw [intervalIntegral.integral_congr_ae hae',
    intervalIntegral.integral_sub hf hg]
  dsimp [g]
  rw [intervalIntegral.integral_indicator ⟨hd0, hdR⟩]
  simp only [f, d]
  change (∫ r in 0..R, (2 : ℝ) * id r) -
      ∫ r in 0..dist z 0, (2 : ℝ) * id r = _
  calc
    (∫ r in 0..R, (2 : ℝ) * id r) -
        ∫ r in 0..dist z 0, (2 : ℝ) * id r =
        2 * (∫ r in 0..R, id r) -
          2 * (∫ r in 0..dist z 0, id r) := by
            rw [intervalIntegral.integral_const_mul,
              intervalIntegral.integral_const_mul]
    _ = R ^ 2 - (dist z 0) ^ 2 := by
      simp [integral_id]
      ring

/-! ## Phase D: finite layer-cake identity -/

/-- The radial layer integrand for the fixed outer disk. -/
noncomputable def pascalCenteredXiZeroDiskLayerIntegrand (R r : ℝ) : ℝ :=
  2 * r * pascalCenteredXiZeroDiskLayerCount R r

/-- Integrating the finite layer count recovers `R² M_R - Q_R`. -/
theorem integral_pascalCenteredXiZeroDiskLayerIntegrand_eq
    {R : ℝ} (hR : 0 ≤ R) :
    (∫ r in 0..R, pascalCenteredXiZeroDiskLayerIntegrand R r) =
      R ^ 2 * (pascalCenteredXiZeroDiskMultiplicity R : ℝ) -
        pascalCenteredXiZeroDiskRadialSecondMoment R := by
  classical
  unfold pascalCenteredXiZeroDiskLayerIntegrand
  unfold pascalCenteredXiZeroDiskLayerCount
  simp_rw [Finset.mul_sum]
  have hpoint : ∀ z r,
      2 * r * (if dist z 0 ≤ r then (pascalCenteredXiZeroMultiplicity z : ℝ) else 0) =
        (pascalCenteredXiZeroMultiplicity z : ℝ) *
          (2 * r * (if dist z 0 ≤ r then (1 : ℝ) else 0)) := by
    intro z r
    split_ifs <;> ring
  simp_rw [hpoint]
  rw [intervalIntegral.integral_finsetSum]
  · simp only [intervalIntegral.integral_const_mul]
    have hterm : ∀ z ∈ pascalCenteredXiZeroDiskFinset R,
        (∫ r in 0..R,
          2 * r * (if dist z 0 ≤ r then (1 : ℝ) else 0)) =
          R ^ 2 - (dist z 0) ^ 2 := by
      intro z hz
      exact intervalIntegral_two_mul_radius_indicator_ge_dist hR hz
    have hsum :
        (∑ z ∈ pascalCenteredXiZeroDiskFinset R,
          (pascalCenteredXiZeroMultiplicity z : ℝ) *
            (∫ r in 0..R,
              2 * r * (if dist z 0 ≤ r then (1 : ℝ) else 0))) =
          ∑ z ∈ pascalCenteredXiZeroDiskFinset R,
            (pascalCenteredXiZeroMultiplicity z : ℝ) *
              (R ^ 2 - (dist z 0) ^ 2) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [hterm z hz]
    rw [hsum]
    calc
      (∑ z ∈ pascalCenteredXiZeroDiskFinset R,
          (pascalCenteredXiZeroMultiplicity z : ℝ) *
            (R ^ 2 - (dist z 0) ^ 2)) =
          ∑ z ∈ pascalCenteredXiZeroDiskFinset R,
            ((pascalCenteredXiZeroMultiplicity z : ℝ) * R ^ 2 -
              (pascalCenteredXiZeroMultiplicity z : ℝ) * (dist z 0) ^ 2) := by
        apply Finset.sum_congr rfl
        intro z hz
        ring
      _ = (∑ z ∈ pascalCenteredXiZeroDiskFinset R,
          (pascalCenteredXiZeroMultiplicity z : ℝ) * R ^ 2) -
          ∑ z ∈ pascalCenteredXiZeroDiskFinset R,
            (pascalCenteredXiZeroMultiplicity z : ℝ) * (dist z 0) ^ 2 := by
        rw [Finset.sum_sub_distrib]
      _ = R ^ 2 * (pascalCenteredXiZeroDiskMultiplicity R : ℝ) -
          pascalCenteredXiZeroDiskRadialSecondMoment R := by
        unfold pascalCenteredXiZeroDiskMultiplicity
        push_cast
        unfold pascalCenteredXiZeroDiskRadialSecondMoment
        simp only [dist_eq_norm, sub_zero]
        have hmass :
            (∑ z ∈ pascalCenteredXiZeroDiskFinset R,
              (pascalCenteredXiZeroMultiplicity z : ℝ) * R ^ 2) =
              R ^ 2 * ∑ z ∈ pascalCenteredXiZeroDiskFinset R,
                (pascalCenteredXiZeroMultiplicity z : ℝ) := by
          rw [← Finset.sum_mul]
          ring
        rw [hmass]
        have hnorm :
            (∑ z ∈ pascalCenteredXiZeroDiskFinset R,
              (pascalCenteredXiZeroMultiplicity z : ℝ) * ‖z‖ ^ 2) =
              ∑ z ∈ pascalCenteredXiZeroDiskFinset R,
                (pascalCenteredXiZeroMultiplicity z : ℝ) * Complex.normSq z := by
          apply Finset.sum_congr rfl
          intro z hz
          rw [Complex.sq_norm]
        rw [hnorm]
  · intro z hz
    exact (intervalIntegrable_two_mul_radius_indicator_ge_dist hR hz).const_mul _

/-- The intrinsic radial moment in finite layer-cake form. -/
theorem pascalCenteredXiZeroDiskRadialSecondMoment_eq_layerCake
    {R : ℝ} (hR : 0 ≤ R) :
    pascalCenteredXiZeroDiskRadialSecondMoment R =
      R ^ 2 * (pascalCenteredXiZeroDiskMultiplicity R : ℝ) -
        (∫ r in 0..R, pascalCenteredXiZeroDiskLayerIntegrand R r) := by
  rw [integral_pascalCenteredXiZeroDiskLayerIntegrand_eq hR]
  ring

/-- The finite layer integrand is interval integrable on a nonnegative radius. -/
theorem intervalIntegrable_pascalCenteredXiZeroDiskLayerIntegrand
    {R : ℝ} (hR : 0 ≤ R) :
    IntervalIntegrable
      (pascalCenteredXiZeroDiskLayerIntegrand R) volume 0 R := by
  classical
  unfold pascalCenteredXiZeroDiskLayerIntegrand
  unfold pascalCenteredXiZeroDiskLayerCount
  simp_rw [Finset.mul_sum]
  have hpoint : ∀ z r,
      2 * r * (if dist z 0 ≤ r then (pascalCenteredXiZeroMultiplicity z : ℝ) else 0) =
        (pascalCenteredXiZeroMultiplicity z : ℝ) *
          (2 * r * (if dist z 0 ≤ r then (1 : ℝ) else 0)) := by
    intro z r
    split_ifs <;> ring
  simp_rw [hpoint]
  rw [show
      (fun r => ∑ x ∈ pascalCenteredXiZeroDiskFinset R,
        (pascalCenteredXiZeroMultiplicity x : ℝ) *
          (2 * r * (if dist x 0 ≤ r then (1 : ℝ) else 0))) =
        (∑ x ∈ pascalCenteredXiZeroDiskFinset R,
          (fun r => (pascalCenteredXiZeroMultiplicity x : ℝ) *
            (2 * r * (if dist x 0 ≤ r then (1 : ℝ) else 0)))) by
    funext r
    simp]
  apply IntervalIntegrable.sum
  intro z hz
  exact (intervalIntegrable_two_mul_radius_indicator_ge_dist hR hz).const_mul _

/-! ## Phase E: fixed Xi outer count -/

/-- The real multiplicity count extracted from the normalized fixed Xi outer contour.

The leading minus is part of the definition because PPW-021 normalizes the
`-Xi'/Xi` contour to the negative multiplicity count. -/
noncomputable def pascalCenteredXiOuterCount (r : ℝ) : ℝ :=
  -((2 * Real.pi * Complex.I)⁻¹ * pascalCenteredXiOuterContourMass r).re

/-- At a boundary-safe radius, the fixed Xi outer count is intrinsic multiplicity. -/
@[simp] theorem pascalCenteredXiOuterCount_eq_zeroDiskMultiplicity
    {r : ℝ} (hr : IsPascalCenteredXiBoundarySafeRadius r) :
    pascalCenteredXiOuterCount r =
      (pascalCenteredXiZeroDiskMultiplicity r : ℝ) := by
  unfold pascalCenteredXiOuterCount
  rw [pascalCenteredXiNormalizedOuterContourMass_eq_zeroDiskMultiplicity hr]
  simp

/-! ## Phase F: bounded forbidden radii -/

/-- Radii created by centered Xi zeros in the fixed outer disk. -/
noncomputable def pascalCenteredXiForbiddenRadii (R : ℝ) : Finset ℝ :=
  (pascalCenteredXiZeroDiskFinset R).image (fun z => dist z 0)

/-- A positive radius up to `R` outside the forbidden set is boundary-safe. -/
theorem isBoundarySafe_of_pos_le_not_mem_forbiddenRadii
    {R r : ℝ} (hr0 : 0 < r) (hrR : r ≤ R)
    (hr : r ∉ pascalCenteredXiForbiddenRadii R) :
    IsPascalCenteredXiBoundarySafeRadius r := by
  rw [isPascalCenteredXiBoundarySafeRadius_iff_no_zero_on_sphere]
  refine ⟨hr0, ?_⟩
  intro z hz hzero
  have hzR : z ∈ pascalCenteredXiZeroDiskFinset R := by
    rw [mem_pascalCenteredXiZeroDiskFinset_iff]
    refine ⟨Metric.mem_closedBall.mpr ?_, hzero⟩
    rw [Metric.mem_sphere.mp hz]
    exact hrR
  apply hr
  refine Finset.mem_image.mpr ⟨z, hzR, ?_⟩
  exact Metric.mem_sphere.mp hz

/-- The forbidden radii in a bounded interval form a finite exceptional set. -/
theorem finite_boundaryUnsafeRadii_in_Icc (R : ℝ) :
    {r : ℝ | r ∈ Set.Icc 0 R ∧
      ¬ IsPascalCenteredXiBoundarySafeRadius r}.Finite := by
  let F := pascalCenteredXiForbiddenRadii R
  have hsub : {r : ℝ | r ∈ Set.Icc 0 R ∧
      ¬ IsPascalCenteredXiBoundarySafeRadius r} ⊆
      ({0} : Set ℝ) ∪ (F : Set ℝ) := by
    intro r hr
    by_cases hrzero : r = 0
    · exact Or.inl (by simp [hrzero])
    · right
      have hr0 : 0 < r := lt_of_le_of_ne hr.1.1 (Ne.symm hrzero)
      by_contra hnot
      exact hr.2 (isBoundarySafe_of_pos_le_not_mem_forbiddenRadii
        hr0 hr.1.2 hnot)
  apply (Set.Finite.union (Set.finite_singleton 0) F.finite_toSet).subset hsub

/-! ## Phase G: almost-everywhere outer-count replacement -/

/-- The layer integrand agrees almost everywhere with the fixed outer-count integrand. -/
theorem pascalCenteredXiZeroDiskLayerIntegrand_ae_eq_outerCountIntegrand
    {R : ℝ} (_hR : 0 < R) :
    (fun r => pascalCenteredXiZeroDiskLayerIntegrand R r) =ᵐ[
      volume.restrict (Set.Ioc 0 R)]
      (fun r => 2 * r * pascalCenteredXiOuterCount r) := by
  let F := pascalCenteredXiForbiddenRadii R
  have hFzero : volume (F : Set ℝ) = 0 := F.finite_toSet.measure_zero volume
  have hFae : ∀ᵐ r ∂volume, r ∉ (F : Set ℝ) := by
    simpa only [ae_iff, Classical.not_not] using! hFzero
  filter_upwards [ae_restrict_of_ae hFae,
    ae_restrict_mem measurableSet_Ioc] with r hrF hrIoc
  change r ∉ F at hrF
  have hrsafe := isBoundarySafe_of_pos_le_not_mem_forbiddenRadii
    hrIoc.1 hrIoc.2 hrF
  have hlayer := pascalCenteredXiZeroDiskLayerCount_eq_multiplicity
    hrIoc.1.le hrIoc.2
  simp [pascalCenteredXiZeroDiskLayerIntegrand, hlayer,
    pascalCenteredXiOuterCount_eq_zeroDiskMultiplicity hrsafe]

/-- The outer-count integrand is interval integrable by finite layer transport. -/
theorem intervalIntegrable_two_mul_radius_mul_pascalCenteredXiOuterCount
    {R : ℝ} (hR : 0 < R) :
    IntervalIntegrable
      (fun r => 2 * r * pascalCenteredXiOuterCount r) volume 0 R := by
  have hae := pascalCenteredXiZeroDiskLayerIntegrand_ae_eq_outerCountIntegrand hR
  have hae' :
      (fun r => pascalCenteredXiZeroDiskLayerIntegrand R r) =ᵐ[
        volume.restrict (uIoc 0 R)]
        (fun r => 2 * r * pascalCenteredXiOuterCount r) := by
    simpa [uIoc_of_le hR.le] using hae
  exact (intervalIntegrable_pascalCenteredXiZeroDiskLayerIntegrand hR.le).congr_ae hae'

/-! ## Phase H: radial moment as fixed outer-count layer cake -/

/-- The Xi radial moment has its fixed outer-count layer-cake representation. -/
theorem pascalCenteredXiZeroDiskRadialSecondMoment_eq_outerCountIntegral
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiZeroDiskRadialSecondMoment R =
      R ^ 2 * (pascalCenteredXiZeroDiskMultiplicity R : ℝ) -
        (∫ r in 0..R, 2 * r * pascalCenteredXiOuterCount r) := by
  rw [pascalCenteredXiZeroDiskRadialSecondMoment_eq_layerCake hR.1.le]
  have hae := pascalCenteredXiZeroDiskLayerIntegrand_ae_eq_outerCountIntegrand hR.1
  have hae' :
      (fun r => pascalCenteredXiZeroDiskLayerIntegrand R r) =ᵐ[
        volume.restrict (uIoc 0 R)]
        (fun r => 2 * r * pascalCenteredXiOuterCount r) := by
    simpa [uIoc_of_le hR.1.le] using hae
  have hae'' := (ae_restrict_iff' measurableSet_uIoc).mp hae'
  rw [intervalIntegral.integral_congr_ae hae'']

/-- The fixed outer count at the endpoint replaces the intrinsic endpoint count. -/
theorem pascalCenteredXiZeroDiskRadialSecondMoment_eq_fixedXiOuterCountLayerCake
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiZeroDiskRadialSecondMoment R =
      R ^ 2 * pascalCenteredXiOuterCount R -
        (∫ r in 0..R, 2 * r * pascalCenteredXiOuterCount r) := by
  rw [pascalCenteredXiZeroDiskRadialSecondMoment_eq_outerCountIntegral hR,
    pascalCenteredXiOuterCount_eq_zeroDiskMultiplicity hR]

/-- The PPW window radial moment has the same fixed Xi outer-count representation. -/
theorem pascalCriticalMirrorZeroWindowRadialSecondMoment_eq_fixedXiOuterCountLayerCake
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCriticalMirrorZeroWindowRadialSecondMoment R =
      R ^ 2 * pascalCenteredXiOuterCount R -
        (∫ r in 0..R, 2 * r * pascalCenteredXiOuterCount r) := by
  rw [← pascalCenteredXiZeroDiskRadialSecondMoment_eq_window]
  exact pascalCenteredXiZeroDiskRadialSecondMoment_eq_fixedXiOuterCountLayerCake hR

/-- The CF2D `q2` radial mass also admits the fixed Xi outer-count form. -/
theorem pascalCriticalMirrorZeroWindowCF2DRadialMass_eq_fixedXiOuterCountLayerCake
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCriticalMirrorZeroWindowCF2DRadialMass R =
      R ^ 2 * pascalCenteredXiOuterCount R -
        (∫ r in 0..R, 2 * r * pascalCenteredXiOuterCount r) := by
  rw [pascalCriticalMirrorZeroWindowCF2DRadialMass_eq]
  exact pascalCriticalMirrorZeroWindowRadialSecondMoment_eq_fixedXiOuterCountLayerCake hR

end DkMath.RH.CFBRCProjection
