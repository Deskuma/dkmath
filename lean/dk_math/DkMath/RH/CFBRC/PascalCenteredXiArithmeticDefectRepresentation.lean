/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiMellinQuadraticArithmeticLimit
import DkMath.RH.CFBRC.PascalCenteredXiFixedSecondMomentDefectBridge
import Mathlib.Tactic

/-!
# Ordered arithmetic representation of the fixed-Xi defect

This module normalizes the XDP-020 quadratic arithmetic endpoint by the same
factor `(2 * π * I)⁻¹` used by the fixed Xi second-contour functional.  It then
subtracts the real part of that normalized arithmetic observable from the
unchanged fixed radial observable.

The resulting representation is ordered: `X → ∞` is taken for each fixed
`ε > 0`, and only the resulting endpoint is sent through `ε → 0+`.  No limit
exchange, joint limit, uniform cutoff estimate, sign theorem for finite
approximants, defect-vanishing theorem, or RH consequence is asserted.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-! ## Gate A: normalized arithmetic observables -/

/-- The XDP-020 finite quadratic arithmetic approximant in fixed-contour
normalization. -/
noncomputable def pascalCenteredXiMellinQuadraticNormalizedArithmeticApproximant
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ *
    pascalCenteredXiMellinQuadraticArithmeticApproximant ε W X

/-- The XDP-020 quadratic arithmetic endpoint in fixed-contour normalization.
-/
noncomputable def pascalCenteredXiMellinQuadraticNormalizedArithmeticEndpoint
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ *
    pascalCenteredXiMellinQuadraticArithmeticEndpoint ε W

/-- The normalized arithmetic endpoint is the negative quadratic-Mellin
zero moment.  The sign records exactly
`(2πi)⁻¹ * (-(2πi) * M) = -M`. -/
theorem pascalCenteredXiMellinQuadraticNormalizedArithmeticEndpoint_eq
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) :
    pascalCenteredXiMellinQuadraticNormalizedArithmeticEndpoint ε W =
      -pascalCenteredXiMellinQuadraticZeroMoment ε W := by
  unfold pascalCenteredXiMellinQuadraticNormalizedArithmeticEndpoint
    pascalCenteredXiMellinQuadraticArithmeticEndpoint
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
    · exact Complex.I_ne_zero
  field_simp [hne]

/-! ## Gate B: fixed-epsilon normalized arithmetic convergence -/

/-- For fixed positive `ε`, normalization transports the XDP-020 `X → ∞`
convergence to the fixed-contour convention.  No uniformity in `ε` is used.
-/
theorem tendsto_pascalCenteredXiMellinQuadraticNormalizedArithmeticApproximant
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    Tendsto
      (fun X =>
        pascalCenteredXiMellinQuadraticNormalizedArithmeticApproximant ε W X)
      atTop
      (nhds
        (pascalCenteredXiMellinQuadraticNormalizedArithmeticEndpoint ε W)) := by
  have hconst : Tendsto (fun _ : ℕ =>
      (2 * Real.pi * Complex.I)⁻¹) atTop
      (nhds ((2 * Real.pi * Complex.I)⁻¹)) := tendsto_const_nhds
  have h := tendsto_pascalCenteredXiMellinQuadraticArithmeticApproximant hε W
  change Tendsto
    (fun X => (2 * Real.pi * Complex.I)⁻¹ *
      pascalCenteredXiMellinQuadraticArithmeticApproximant ε W X)
    atTop
    (nhds ((2 * Real.pi * Complex.I)⁻¹ *
      (-(2 * Real.pi * Complex.I) *
        pascalCenteredXiMellinQuadraticZeroMoment ε W)))
  exact hconst.mul h

/-! ## Gate C: normalized epsilon closure -/

/-- The normalized arithmetic endpoint converges through `ε → 0+` to the
fixed holomorphic second-contour functional.  This is a scalar normalization
of the XDP-020 endpoint theorem, not a new contour calculation. -/
theorem tendsto_pascalCenteredXiMellinQuadraticNormalizedArithmeticEndpoint_epsilon
    (W : PascalCenteredXiResidueTransportWindow) :
    Tendsto
      (fun ε : ℝ =>
        pascalCenteredXiMellinQuadraticNormalizedArithmeticEndpoint ε W)
      (𝓝[>] 0)
      (nhds
        (pascalCenteredXiFixedHolomorphicSecondContourFunctional W.R)) := by
  have hconst : Tendsto (fun _ : ℝ =>
      (2 * Real.pi * Complex.I)⁻¹) (𝓝[>] 0)
      (nhds ((2 * Real.pi * Complex.I)⁻¹)) := tendsto_const_nhds
  have h := tendsto_pascalCenteredXiMellinQuadraticArithmeticEndpoint_secondContour W
  simpa [pascalCenteredXiMellinQuadraticNormalizedArithmeticEndpoint,
    pascalCenteredXiFixedHolomorphicSecondContourFunctional] using
    hconst.mul h

/-! ## Gate D: arithmetic defect approximant and endpoint -/

/-- The finite arithmetic defect approximant: the fixed radial observable is
kept independent of both `ε` and `X`, while only the normalized arithmetic
holomorphic approximant varies. -/
noncomputable def pascalCenteredXiMellinQuadraticArithmeticDefectApproximant
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℝ :=
  pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
    (pascalCenteredXiMellinQuadraticNormalizedArithmeticApproximant ε W X).re

/-- The ordered arithmetic defect endpoint obtained after the inner cutoff
limit, with the same fixed radial observable. -/
noncomputable def pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
    (pascalCenteredXiMellinQuadraticNormalizedArithmeticEndpoint ε W).re

/-! ## Gate E: fixed-epsilon defect convergence -/

/-- At fixed positive `ε`, the finite arithmetic defect approximants converge
to the corresponding arithmetic defect endpoint by continuity of `Complex.re`
and subtraction from a constant.  No sign assertion is made for any finite
cutoff value. -/
theorem tendsto_pascalCenteredXiMellinQuadraticArithmeticDefectApproximant
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    Tendsto
      (fun X =>
        pascalCenteredXiMellinQuadraticArithmeticDefectApproximant ε W X)
      atTop
      (nhds
        (pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint ε W)) := by
  have h := tendsto_pascalCenteredXiMellinQuadraticNormalizedArithmeticApproximant
    hε W
  have hre := (Complex.continuous_re.tendsto _).comp h
  have hconst : Tendsto (fun _ : ℕ =>
      pascalCenteredXiFixedRadialSecondMomentFunctional W.R) atTop
      (nhds (pascalCenteredXiFixedRadialSecondMomentFunctional W.R)) :=
    tendsto_const_nhds
  simpa [pascalCenteredXiMellinQuadraticArithmeticDefectApproximant,
    pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint] using
    hconst.sub hre

/-! ## Gate F: defect endpoint epsilon closure -/

/-- The ordered arithmetic defect endpoint converges as `ε → 0+` to the
existing fixed-Xi second-moment defect.  The proof only transports the
normalized holomorphic endpoint through `Complex.re` and fixed subtraction.
-/
theorem tendsto_pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint_epsilon
    (W : PascalCenteredXiResidueTransportWindow) :
    Tendsto
      (fun ε : ℝ =>
        pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint ε W)
      (𝓝[>] 0)
      (nhds
        (pascalCenteredXiFixedSecondMomentDefectFunctional W.R)) := by
  have h := tendsto_pascalCenteredXiMellinQuadraticNormalizedArithmeticEndpoint_epsilon W
  have hre := (Complex.continuous_re.tendsto _).comp h
  have hconst : Tendsto (fun _ : ℝ =>
      pascalCenteredXiFixedRadialSecondMomentFunctional W.R) (𝓝[>] 0)
      (nhds (pascalCenteredXiFixedRadialSecondMomentFunctional W.R)) :=
    tendsto_const_nhds
  simpa [pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint,
    pascalCenteredXiFixedSecondMomentDefectFunctional] using
    hconst.sub hre

/-! ## Gate G: ordered prime-side defect certificate -/

/-- The ordered prime-side defect representation certificate.  It records
`lim ε→0+ (lim X→∞ D(ε,X,W))` and does not assert the reverse order, a joint
limit, uniform convergence, or any sign of the approximants. -/
theorem pascalCenteredXiMellinQuadraticArithmeticDefectIteratedLimitCertificate
    (W : PascalCenteredXiResidueTransportWindow) :
    (∀ ε : ℝ, 0 < ε →
      Tendsto
        (fun X =>
          pascalCenteredXiMellinQuadraticArithmeticDefectApproximant ε W X)
        atTop
        (nhds
          (pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint ε W))) ∧
    Tendsto
      (fun ε : ℝ =>
        pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint ε W)
      (𝓝[>] 0)
      (nhds
        (pascalCenteredXiFixedSecondMomentDefectFunctional W.R)) := by
  constructor
  · intro ε hε
    exact tendsto_pascalCenteredXiMellinQuadraticArithmeticDefectApproximant hε W
  · exact tendsto_pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint_epsilon W

/-! ## Gate H: finite von Mangoldt defect surface -/

/-- The finite defect approximant is explicitly the fixed radial observable
minus the real part of the normalized XDP-020 finite von Mangoldt surface. -/
theorem pascalCenteredXiMellinQuadraticArithmeticDefectApproximant_eq_vonMangoldt_surface
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinQuadraticArithmeticDefectApproximant ε W X =
      pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
        (((2 * Real.pi * Complex.I)⁻¹ *
          (2 * (∑ n ∈ Finset.range (X + 1),
            ∫ t in (-W.rectangle.T)..W.rectangle.T,
              (pascalCenteredXiMellinSecondDifferenceWeight ε 0
                (pascalOrdinaryToCentered
                  (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
                ((ArithmeticFunction.vonMangoldt n : ℂ) *
                  ((n : ℂ) ^
                    (-(pascalSymmetricRectangleRightEdge W.rectangle.σ t)))) *
                Complex.I)) +
          2 * pascalXiArchimedeanRightEdgeIntegral
            (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
            W.rectangle.σ W.rectangle.T +
          2 * pascalXiElementaryRightEdgeIntegral
            (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
            W.rectangle.σ W.rectangle.T +
          2 * pascalCenteredXiTopHorizontalContribution
            (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
            W.toContourTransportWindow)).re) := by
  unfold pascalCenteredXiMellinQuadraticArithmeticDefectApproximant
    pascalCenteredXiMellinQuadraticNormalizedArithmeticApproximant
  rw [pascalCenteredXiMellinQuadraticArithmeticApproximant_eq_vonMangoldt_sum
    hε W X]

/-! ## Gate I: CF2D compatibility -/

/-- The finite arithmetic defect surface can use the existing CF2D radial
observable on a safe radius.  This is only a target rewrite; it supplies no
sign theorem for the arithmetic approximants. -/
theorem pascalCenteredXiMellinQuadraticArithmeticDefectApproximant_eq_cf2dRadial_sub_normalized
    {ε : ℝ} (_hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinQuadraticArithmeticDefectApproximant ε W X =
      pascalCriticalMirrorZeroWindowCF2DRadialMass W.R -
        (pascalCenteredXiMellinQuadraticNormalizedArithmeticApproximant
          ε W X).re := by
  unfold pascalCenteredXiMellinQuadraticArithmeticDefectApproximant
  rw [pascalCenteredXiFixedRadialSecondMomentFunctional_eq_cf2dRadial
    W.circle_safe]

end DkMath.RH.CFBRCProjection
