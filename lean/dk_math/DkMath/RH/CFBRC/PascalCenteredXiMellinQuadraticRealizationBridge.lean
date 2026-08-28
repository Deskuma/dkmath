/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.MellinMultiplicativeApproxIdentity
import DkMath.RH.CFBRC.PascalCenteredXiMellinSecondDifferenceBridge
import DkMath.RH.CFBRC.PascalCenteredXiOuterContourResidueBridge
import Mathlib.Tactic

/-!
# Multiplicative approximate identities and the centered Xi second moment

This module is the XDP-007 bridge.  The ordinary compact-support box
`centeredMellinBoxApprox ε` has centered Mellin weight converging pointwise to
one as `ε → 0⁺`.  The finite centered-Xi zero-disk sum therefore converges to
the existing quadratic moment.  For each fixed positive `ε`, the XDP-006
second-difference contour theorem applies to the same box family.

The two limits are kept separate: this file proves the `τ → 0` statement for
fixed `ε`, and then the `ε → 0⁺` statement for its target.  No joint limit in
`(ε, τ)` is asserted.  The result is an ordinary compact-support realization;
it is not a Dirac distribution, a global exact interpolation theorem, a
prime-side formula, a defect-vanishing theorem, or an RH theorem.
-/

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open Filter
open scoped Topology

/-! ## Gate F: finite quadratic realization -/

/-- The finite centered-Xi weighted moment of the box family converges to the
existing centered Xi second moment as the logarithmic box shrinks.

This is a finite-sum theorem.  It uses pointwise convergence of
`z ^ 2 * H_ε(z)` and does not require a uniform estimate over the zero disk. -/
theorem tendsto_pascalCenteredXiZeroDiskMellinBoxQuadraticMoment_secondMoment
    {R : ℝ} :
    Tendsto
      (fun ε : ℝ =>
        pascalCenteredXiZeroDiskWeightedMoment
          (fun z =>
            z ^ 2 * centeredMellinSpectralWeight
              (centeredMellinBoxApprox ε) z)
          R)
      (𝓝[>] 0)
      (𝓝 (pascalCenteredXiZeroDiskSecondMoment R)) := by
  classical
  unfold pascalCenteredXiZeroDiskWeightedMoment
  apply tendsto_finsetSum
  intro a ha
  exact tendsto_const_nhds.mul
    (tendsto_centeredMellinBoxApprox_quadraticWeight a)

/-! ## Gate G: fixed-ε XDP-006 specialization -/

/-- For a fixed positive box width, the normalized fixed-Xi outer contour of
the centered Mellin second difference converges as `τ → 0` to the negative
finite quadratic Mellin-weighted moment.

The support and continuity obligations are discharged by the ordinary box
family.  The safe-radius hypothesis is retained exactly where the residue
bridge requires it. -/
theorem tendsto_pascalCenteredXiNormalizedMellinBoxSecondDifferenceOuterContourMass_tau
    {ε R : ℝ} (hε : 0 < ε)
    (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    Tendsto
      (fun τ : ℝ =>
        (2 * Real.pi * Complex.I)⁻¹ *
          pascalCenteredXiWeightedOuterContourMass
            (centeredMellinSecondDifferenceWeight
              (centeredMellinBoxApprox ε) τ) R)
      (𝓝 0)
      (𝓝
        (-pascalCenteredXiZeroDiskWeightedMoment
          (fun z =>
            z ^ 2 * centeredMellinSpectralWeight
              (centeredMellinBoxApprox ε) z)
          R)) := by
  exact tendsto_pascalCenteredXiNormalizedMellinSecondDifferenceOuterContourMass
    (h := centeredMellinBoxApprox ε)
    (a := Real.exp (-ε)) (b := Real.exp ε) (R := R)
    (Real.exp_pos (-ε))
    (centeredMellinBoxApprox_endpoints_ordered hε)
    (centeredMellinBoxApprox_support_subset hε)
    (centeredMellinBoxApprox_continuousOn hε)
    hR

/-! ## Gate F followed by Gate G: the iterated target -/

/-- The `ε → 0⁺` limit of the fixed-`ε` contour target is the negative
centered Xi second moment.

This theorem records the outer limit of the fixed-`ε` `τ`-limit.  It does not
claim that the two parameters admit a product-filter (joint) limit. -/
theorem tendsto_pascalCenteredXiMellinBoxQuadraticNormalizedContourTarget
    {R : ℝ} :
    Tendsto
      (fun ε : ℝ =>
        -pascalCenteredXiZeroDiskWeightedMoment
          (fun z =>
            z ^ 2 * centeredMellinSpectralWeight
              (centeredMellinBoxApprox ε) z)
          R)
      (𝓝[>] 0)
      (𝓝 (-pascalCenteredXiZeroDiskSecondMoment R)) := by
  have hmoment :=
    tendsto_pascalCenteredXiZeroDiskMellinBoxQuadraticMoment_secondMoment
      (R := R)
  simpa using hmoment.neg

/-! ## Gate H: return to the fixed second contour -/

/-- The iterated box-family target is exactly the target of the existing
fixed `z ^ 2` centered-Xi contour theorem at every boundary-safe radius.

No new residue calculation is performed here; the equality is the existing
fixed-contour API with its safe-radius hypothesis. -/
theorem pascalCenteredXiMellinBoxQuadraticLimit_eq_fixedSecondContourTarget
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    -pascalCenteredXiZeroDiskSecondMoment R =
      (2 * Real.pi * Complex.I)⁻¹ *
        pascalCenteredXiSecondOuterContourMass R := by
  symm
  exact pascalCenteredXiNormalizedSecondOuterContourMass_eq_zeroDiskSecondMoment hR

end DkMath.RH.CFBRCProjection
