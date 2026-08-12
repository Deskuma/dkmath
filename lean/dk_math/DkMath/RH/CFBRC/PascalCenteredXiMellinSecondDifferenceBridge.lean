/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.MellinCenteredDilation
import DkMath.RH.CFBRC.PascalCenteredXiMellinWeightedOuterContourBridge
import Mathlib.Tactic

/-!
# Mellin centered second differences on the fixed Xi contour

This module lifts the pointwise centered-dilation limit from the generic
Mellin analysis module to the finite centered-Xi zero disk and then applies the
existing fixed-Xi normalized outer-contour theorem.  All sums here are finite;
no safe-radius hypothesis is needed for the finite-sum limit itself.

The resulting limit has the exact target
`z ^ 2 * centeredMellinSpectralWeight h z`.  The factor supplied by the
ordinary Mellin test function is retained.  In particular, this module does
not construct an `h` with centered weight identically one, does not identify a
hard zero-window indicator with a Mellin transform, and does not provide a
defect-vanishing or RH theorem.  The realization problem is intentionally
handed to XDP-007.
-/

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open Filter
open scoped Topology

/-! ## Finite centered-Xi moment transport -/

/-- The finite centered-Xi weighted moment of the patched Mellin second
difference converges to the corresponding quadratic Mellin-weighted moment.

The proof uses only pointwise convergence and finite-sum continuity, so the
boundary-safe-radius contract is deliberately absent from this theorem. -/
theorem tendsto_pascalCenteredXiZeroDiskMellinSecondDifferenceMoment
    {h : ℝ → ℂ} {R : ℝ} :
    Tendsto
      (fun τ : ℝ =>
        pascalCenteredXiZeroDiskWeightedMoment
          (centeredMellinSecondDifferenceWeight h τ) R)
      (𝓝 0)
      (𝓝
        (pascalCenteredXiZeroDiskWeightedMoment
          (fun z => z ^ 2 * centeredMellinSpectralWeight h z) R)) := by
  classical
  unfold pascalCenteredXiZeroDiskWeightedMoment
  apply tendsto_finsetSum
  intro a ha
  exact tendsto_const_nhds.mul
    (tendsto_centeredMellinSecondDifferenceWeight_zero a)

/-! ## Thin fixed-Xi contour bridge -/

/-- The normalized fixed-Xi outer contour for a centered Mellin second
difference equals the negative finite weighted zero-disk moment.

This is a thin application of the generic residue theorem.  Pole subtraction,
removable patches, and the Cauchy integral argument remain in the existing
fixed-Xi module. -/
theorem pascalCenteredXiNormalizedMellinSecondDifferenceOuterContourMass_eq
    {h : ℝ → ℂ} {a b R τ : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support h ⊆ Set.Icc a b)
    (hcont : ContinuousOn h (Set.Icc a b))
    (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    (2 * Real.pi * Complex.I)⁻¹ *
        pascalCenteredXiWeightedOuterContourMass
          (centeredMellinSecondDifferenceWeight h τ) R =
      -pascalCenteredXiZeroDiskWeightedMoment
        (centeredMellinSecondDifferenceWeight h τ) R := by
  exact pascalCenteredXiNormalizedWeightedOuterContourMass_eq
    (differentiable_centeredMellinSecondDifferenceWeight
      ha hab hsupp hcont) hR

/-- The normalized fixed-Xi contour family converges to the negative
quadratic Mellin-weighted zero-disk moment at every boundary-safe radius. -/
theorem tendsto_pascalCenteredXiNormalizedMellinSecondDifferenceOuterContourMass
    {h : ℝ → ℂ} {a b R : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support h ⊆ Set.Icc a b)
    (hcont : ContinuousOn h (Set.Icc a b))
    (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    Tendsto
      (fun τ : ℝ =>
        (2 * Real.pi * Complex.I)⁻¹ *
          pascalCenteredXiWeightedOuterContourMass
            (centeredMellinSecondDifferenceWeight h τ) R)
      (𝓝 0)
      (𝓝
        (-pascalCenteredXiZeroDiskWeightedMoment
          (fun z => z ^ 2 * centeredMellinSpectralWeight h z) R)) := by
  have hmoment := tendsto_pascalCenteredXiZeroDiskMellinSecondDifferenceMoment
    (h := h) (R := R)
  have hneg := hmoment.neg
  apply hneg.congr'
  filter_upwards [] with τ
  exact (pascalCenteredXiNormalizedMellinSecondDifferenceOuterContourMass_eq
    (τ := τ) ha hab hsupp hcont hR).symm

/-! ## Conditional XDP-007 interpolation adapter -/

/-- If the centered Mellin weight interpolates the constant one on the fixed
finite zero disk, the quadratic Mellin-weighted moment reduces to the existing
centered Xi second moment.

This is only a conditional finite adapter.  The interpolation hypothesis is
not an existence statement; constructing a compact-support family satisfying
it remains the named XDP-007 realization gap. -/
theorem pascalCenteredXiZeroDiskWeightedQuadraticMoment_eq_secondMoment_of_interpolates_one
    {h : ℝ → ℂ} {R : ℝ}
    (hinterp : ∀ z ∈ pascalCenteredXiZeroDiskFinset R,
      centeredMellinSpectralWeight h z = 1) :
    pascalCenteredXiZeroDiskWeightedMoment
        (fun z => z ^ 2 * centeredMellinSpectralWeight h z) R =
      pascalCenteredXiZeroDiskSecondMoment R := by
  unfold pascalCenteredXiZeroDiskWeightedMoment pascalCenteredXiZeroDiskSecondMoment
  apply Finset.sum_congr rfl
  intro a ha
  change (pascalCenteredXiZeroMultiplicity a : ℂ) *
      (a ^ 2 * centeredMellinSpectralWeight h a) =
    (pascalCenteredXiZeroMultiplicity a : ℂ) * a ^ 2
  rw [hinterp a ha]
  simp

end DkMath.RH.CFBRCProjection
