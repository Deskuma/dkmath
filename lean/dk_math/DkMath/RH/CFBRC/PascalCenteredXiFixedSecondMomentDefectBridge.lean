/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiRadialLayerCakeOuterCountBridge
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.PascalCenteredXiFixedSecondMomentDefectBridge"

/-!
# Fixed centered-Xi second-moment defect functional

This module packages the fixed centered-Xi representations established in
PPW-021 and PPW-022 into one zero-list-free finite defect functional.  On a
boundary-safe radius it is exactly the existing finite second-moment defect,
and hence exactly twice the finite horizontal energy.

The radial term is defined by the fixed Xi outer-count layer cake, while the
holomorphic term is the normalized fixed `z ^ 2` Xi outer contour.  The radial
quantity is therefore not treated as a holomorphic contour weight.

This is a representation and frontier-audit module.  It does not prove that
the functional vanishes.  Vanishing on every boundary-safe radius is shown to
be equivalent to the formal Riemann hypothesis, so it is recorded as an RH
frontier rather than as an independent provider.  No unsafe-radius residue
identity, prime-side termwise identity, or `R → ∞` passage is introduced.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology Interval

/-! ## Phase A: fixed Xi radial functional -/

/- The functional is intentionally expressed only through the fixed Xi outer
   count and its interval layer-cake integral.  It does not expose the finite
   zero list or the radial `Complex.normSq` definition used in PPW-022. -/
/-- The fixed centered-Xi radial second-moment observable. -/
noncomputable def pascalCenteredXiFixedRadialSecondMomentFunctional
    (R : ℝ) : ℝ :=
  R ^ 2 * pascalCenteredXiOuterCount R -
    (∫ r in 0..R, 2 * r * pascalCenteredXiOuterCount r)

/-- On a boundary-safe radius, the fixed radial observable is the PPW window radial moment. -/
theorem pascalCenteredXiFixedRadialSecondMomentFunctional_eq_windowRadial
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiFixedRadialSecondMomentFunctional R =
      pascalCriticalMirrorZeroWindowRadialSecondMoment R := by
  unfold pascalCenteredXiFixedRadialSecondMomentFunctional
  exact (pascalCriticalMirrorZeroWindowRadialSecondMoment_eq_fixedXiOuterCountLayerCake hR).symm

/-- The fixed radial observable agrees exactly with the CF2D `q2` radial mass. -/
theorem pascalCenteredXiFixedRadialSecondMomentFunctional_eq_cf2dRadial
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiFixedRadialSecondMomentFunctional R =
      pascalCriticalMirrorZeroWindowCF2DRadialMass R := by
  rw [pascalCenteredXiFixedRadialSecondMomentFunctional_eq_windowRadial hR,
    pascalCriticalMirrorZeroWindowCF2DRadialMass_eq]

/-! ## Phase B: fixed Xi holomorphic second-contour functional -/

/- The normalization is the PPW-021 convention: this quantity reads the
   negative centered complex second moment at a safe radius. -/
/-- The normalized fixed centered-Xi `z ^ 2` outer-contour observable. -/
noncomputable def pascalCenteredXiFixedHolomorphicSecondContourFunctional
    (R : ℝ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ *
    pascalCenteredXiSecondOuterContourMass R

/-- At a boundary-safe radius, the normalized fixed contour is the negative centered moment. -/
theorem pascalCenteredXiFixedHolomorphicSecondContourFunctional_eq
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiFixedHolomorphicSecondContourFunctional R =
      -pascalCriticalMirrorZeroWindowCenteredSecondMoment R := by
  unfold pascalCenteredXiFixedHolomorphicSecondContourFunctional
  exact pascalCenteredXiNormalizedSecondOuterContourMass_eq_windowCenteredSecondMoment hR

/-! ## Phase C: full fixed-Xi defect -/

/- This is the theorem-facing scalar functional.  Its definition contains no
   zero Finset, zero multiplicity, mirror-frozen weight, or `Complex.normSq`. -/
/-- The full fixed centered-Xi second-moment defect functional. -/
noncomputable def pascalCenteredXiFixedSecondMomentDefectFunctional
    (R : ℝ) : ℝ :=
  pascalCenteredXiFixedRadialSecondMomentFunctional R -
    (pascalCenteredXiFixedHolomorphicSecondContourFunctional R).re

/-- On safe radii, the fixed Xi defect is the existing finite-window defect. -/
@[simp] theorem pascalCenteredXiFixedSecondMomentDefectFunctional_eq_existing
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiFixedSecondMomentDefectFunctional R =
      pascalCriticalMirrorZeroWindowSecondMomentDefect R := by
  unfold pascalCenteredXiFixedSecondMomentDefectFunctional
  rw [pascalCenteredXiFixedRadialSecondMomentFunctional_eq_windowRadial hR]
  exact (pascalSecondMomentDefect_eq_radial_sub_centeredXiOuter_re hR).symm

/-! ## Phase D: energy and finite zero detectors -/

/-- The fixed Xi defect is exactly twice the finite horizontal energy. -/
theorem pascalCenteredXiFixedSecondMomentDefectFunctional_eq_two_mul_horizontalEnergy
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiFixedSecondMomentDefectFunctional R =
      2 * pascalCriticalMirrorZeroWindowHorizontalEnergy R := by
  rw [pascalCenteredXiFixedSecondMomentDefectFunctional_eq_existing hR,
    pascalCriticalMirrorZeroWindowSecondMomentDefect_eq]

/-- The fixed Xi defect is nonnegative on a boundary-safe finite window. -/
theorem pascalCenteredXiFixedSecondMomentDefectFunctional_nonneg
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    0 ≤ pascalCenteredXiFixedSecondMomentDefectFunctional R := by
  rw [pascalCenteredXiFixedSecondMomentDefectFunctional_eq_two_mul_horizontalEnergy hR]
  exact mul_nonneg (by norm_num) (pascalCriticalMirrorZeroWindowHorizontalEnergy_nonneg R)

/-- Vanishing of the fixed Xi defect detects that every window zero is critical. -/
theorem pascalCenteredXiFixedSecondMomentDefectFunctional_eq_zero_iff
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiFixedSecondMomentDefectFunctional R = 0 ↔
      ∀ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
        ρ.re = (1 : ℝ) / 2 := by
  rw [pascalCenteredXiFixedSecondMomentDefectFunctional_eq_two_mul_horizontalEnergy hR]
  constructor
  · intro hzero
    apply (pascalCriticalMirrorZeroWindowHorizontalEnergy_eq_zero_iff R).mp
    linarith
  · intro hcritical
    have henergy :=
      (pascalCriticalMirrorZeroWindowHorizontalEnergy_eq_zero_iff R).mpr hcritical
    simp [henergy]

/-- Positivity of the fixed Xi defect detects an off-critical window zero. -/
theorem pascalCenteredXiFixedSecondMomentDefectFunctional_pos_iff
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    0 < pascalCenteredXiFixedSecondMomentDefectFunctional R ↔
      ∃ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
        ρ.re ≠ (1 : ℝ) / 2 := by
  rw [pascalCenteredXiFixedSecondMomentDefectFunctional_eq_existing hR]
  exact pascalCriticalMirrorZeroWindowSecondMomentDefect_pos_iff R

/-! ## Phase E: prime-mirror zero-condition compatibility -/

/-- The fixed Xi defect and prime-mirror energy have the same zero condition. -/
theorem pascalCenteredXiFixedSecondMomentDefectFunctional_eq_zero_iff_primeMirrorEnergy
    {n : ℕ} (hn : 1 < n)
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiFixedSecondMomentDefectFunctional R = 0 ↔
      pascalCriticalMirrorZeroWindowEnergy n R = 0 := by
  rw [pascalCenteredXiFixedSecondMomentDefectFunctional_eq_existing hR]
  exact pascalCriticalMirrorZeroWindowSecondMomentDefect_eq_zero_iff hn R

/-! ## Phase F: CF2D and fixed Xi contour -/

/-- The fixed Xi defect is CF2D radial `q2` mass minus the contour real part. -/
theorem pascalCenteredXiFixedSecondMomentDefectFunctional_eq_cf2d_sub_secondContour_re
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiFixedSecondMomentDefectFunctional R =
      pascalCriticalMirrorZeroWindowCF2DRadialMass R -
        (pascalCenteredXiFixedHolomorphicSecondContourFunctional R).re := by
  unfold pascalCenteredXiFixedSecondMomentDefectFunctional
  rw [pascalCenteredXiFixedRadialSecondMomentFunctional_eq_cf2dRadial hR]

/-! ## Phase G: global RH frontier audit -/

/-- The fixed Xi defect vanishes at every boundary-safe finite radius. -/
def PascalCenteredXiFixedDefectVanishesOnSafeRadii : Prop :=
  ∀ R : ℝ,
    IsPascalCenteredXiBoundarySafeRadius R →
      pascalCenteredXiFixedSecondMomentDefectFunctional R = 0

/--
The global fixed-Xi defect-vanishing condition is exactly the formal RH
frontier.  This theorem transports the finite detector in both directions;
it does not provide an independent proof that the defect vanishes.
-/
theorem pascalCenteredXiFixedDefectVanishesOnSafeRadii_iff_riemannHypothesis :
    PascalCenteredXiFixedDefectVanishesOnSafeRadii ↔
      RiemannHypothesis := by
  constructor
  · intro hvanishes
    rw [riemannHypothesis_iff_nontrivialZero_re_eq_half]
    intro ρ hρ
    obtain ⟨R, hρR, hR⟩ :=
      exists_isPascalCenteredXiBoundarySafeRadius_gt (dist ρ criticalLineCenter)
    have hdef := hvanishes R hR
    have hexisting : pascalCriticalMirrorZeroWindowSecondMomentDefect R = 0 := by
      rw [← pascalCenteredXiFixedSecondMomentDefectFunctional_eq_existing hR]
      exact hdef
    have henergy : pascalCriticalMirrorZeroWindowHorizontalEnergy R = 0 := by
      rw [pascalCriticalMirrorZeroWindowSecondMomentDefect_eq] at hexisting
      linarith
    have hρwindow : ρ ∈ pascalCriticalMirrorZeroWindowFinset R := by
      rw [mem_pascalCriticalMirrorZeroWindowFinset_iff]
      refine ⟨Metric.mem_closedBall.mpr (le_of_lt hρR), hρ⟩
    exact (pascalCriticalMirrorZeroWindowHorizontalEnergy_eq_zero_iff R).mp
      henergy ρ hρwindow
  · intro hRH R hR
    rw [pascalCenteredXiFixedSecondMomentDefectFunctional_eq_existing hR,
      pascalCriticalMirrorZeroWindowSecondMomentDefect_eq]
    have hcritical :
        ∀ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
          ρ.re = (1 : ℝ) / 2 := by
      intro ρ hρ
      exact (riemannHypothesis_iff_nontrivialZero_re_eq_half.mp hRH) ρ
        ((mem_pascalCriticalMirrorZeroWindowFinset_iff.mp hρ).2)
    have henergy :=
      (pascalCriticalMirrorZeroWindowHorizontalEnergy_eq_zero_iff R).mpr hcritical
    simp [henergy]

end DkMath.RH.CFBRCProjection
