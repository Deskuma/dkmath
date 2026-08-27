/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiMellinArithmeticSpecialization
import DkMath.RH.CFBRC.PascalCenteredXiMellinQuadraticRealizationBridge
import Mathlib.Tactic

/-!
# Tau-zero quadratic arithmetic endpoint

This module closes the ordered XDP-020 chain.  The XDP-019 arithmetic
specialization is first instantiated at the definitionally patched value
`τ = 0`.  For every fixed positive `ε`, the finite Pascal/von Mangoldt
approximant then tends as `X → ∞` to the quadratic-Mellin finite Xi moment.
The resulting finite zero-side moment is sent along the positive-epsilon
filter by the existing XDP-007 finite-sum theorem.

The order is deliberately fixed: `X → ∞` at fixed `ε > 0`, then `ε → 0+`.
No exchange of these limits, joint filter limit, limit inside a right-edge or
horizontal integral, `T → ∞`, defect conclusion, or RH consequence is stated.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open Filter
open scoped Topology

/-! ## Gate A: exact tau-zero zero-moment bridge -/

/-- The quadratic-Mellin finite zero moment is the XDP-019 named zero moment
at the definitionally patched value `τ = 0`. -/
noncomputable def pascalCenteredXiMellinQuadraticZeroMoment
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℂ :=
  pascalCenteredXiMellinSecondDifferenceZeroMoment ε 0 W

/-- At `τ = 0`, the named Mellin zero moment is exactly the finite
`z² * centeredMellinSpectralWeight` moment.  No positive-epsilon hypothesis
is mathematically needed for this definitional bridge. -/
theorem pascalCenteredXiMellinSecondDifferenceZeroMoment_tau_zero_eq
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow) :
    pascalCenteredXiMellinSecondDifferenceZeroMoment ε 0 W =
      pascalCenteredXiZeroDiskWeightedMoment
        (fun z => z ^ 2 * centeredMellinSpectralWeight
          (centeredMellinBoxApprox ε) z) W.R := by
  unfold pascalCenteredXiMellinSecondDifferenceZeroMoment
  apply congrArg (fun q => pascalCenteredXiZeroDiskWeightedMoment q W.R)
  funext z
  simp [pascalCenteredXiMellinSecondDifferenceWeight,
    centeredMellinSecondDifferenceWeight]

/-! ## Gate B: fixed-epsilon quadratic finite formula -/

/-- The exact finite four-term explicit formula at `τ = 0`.  All correction
and top terms use the same patched Mellin weight and remain at finite height.
-/
theorem pascalCenteredXiMellinQuadraticFiniteExplicitFormula
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    -(2 * Real.pi * Complex.I) *
        pascalCenteredXiMellinQuadraticZeroMoment ε W =
      2 * pascalXiOrdinaryZetaRightEdgeIntegral
          (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
          W.rectangle.σ W.rectangle.T +
      2 * pascalXiArchimedeanRightEdgeIntegral
          (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
          W.rectangle.σ W.rectangle.T +
      2 * pascalXiElementaryRightEdgeIntegral
          (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
          W.rectangle.σ W.rectangle.T +
      2 * pascalCenteredXiTopHorizontalContribution
          (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
          W.toContourTransportWindow := by
  simpa [pascalCenteredXiMellinQuadraticZeroMoment] using
    (pascalCenteredXiMellinFiniteExplicitFormula (ε := ε) (τ := 0) hε W)

/-! ## Gate C: fixed-epsilon quadratic arithmetic approximant -/

/-- The finite arithmetic approximant obtained from XDP-019 by fixing
`τ = 0`. -/
noncomputable def pascalCenteredXiMellinQuadraticArithmeticApproximant
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℂ :=
  pascalCenteredXiMellinFiniteArithmeticApproximant ε 0 W X

/-- For fixed positive `ε`, the quadratic arithmetic approximant tends as
`X → ∞` to its quadratic-Mellin finite Xi endpoint.  The theorem does not
vary `ε` or exchange the two limits. -/
theorem tendsto_pascalCenteredXiMellinQuadraticArithmeticApproximant
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    Tendsto
      (fun X => pascalCenteredXiMellinQuadraticArithmeticApproximant ε W X)
      atTop
      (nhds (-(2 * Real.pi * Complex.I) *
        pascalCenteredXiMellinQuadraticZeroMoment ε W)) := by
  simpa [pascalCenteredXiMellinQuadraticArithmeticApproximant,
    pascalCenteredXiMellinQuadraticZeroMoment,
    pascalCenteredXiMellinSecondDifferenceZeroMoment] using
    (tendsto_pascalCenteredXiMellinFiniteArithmeticExplicitFormula
      (ε := ε) (τ := 0) hε W)

/-! ## Gate D: finite von Mangoldt quadratic surface -/

/-- The fixed-`ε`, `τ = 0` arithmetic surface in finite von Mangoldt form.
The `Complex.cpow` kernel and all correction terms retain the exact XDP-019
shape; the Mellin spectral weight is not replaced by `1`. -/
theorem pascalCenteredXiMellinQuadraticArithmeticApproximant_eq_vonMangoldt_sum
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinQuadraticArithmeticApproximant ε W X =
      2 * (∑ n ∈ Finset.range (X + 1),
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
        W.toContourTransportWindow := by
  simpa [pascalCenteredXiMellinQuadraticArithmeticApproximant] using
    (pascalCenteredXiMellinFiniteArithmeticApproximant_eq_vonMangoldt_sum
      (ε := ε) (τ := 0) hε W X)

/-! ## Gate E: epsilon zero-side closure -/

/-- The quadratic-Mellin finite zero moment converges to the centered Xi
second moment as `ε → 0+`.  This is an existing finite zero-disk sum theorem;
it does not exchange `ε` with any right-edge, correction, or top integral. -/
theorem tendsto_pascalCenteredXiMellinQuadraticZeroMoment_epsilon
    (W : PascalCenteredXiResidueTransportWindow) :
    Tendsto
      (fun ε : ℝ => pascalCenteredXiMellinQuadraticZeroMoment ε W)
      (𝓝[>] 0)
      (nhds (pascalCenteredXiZeroDiskSecondMoment W.R)) := by
  have hbase := tendsto_pascalCenteredXiZeroDiskMellinBoxQuadraticMoment_secondMoment
    (R := W.R)
  apply hbase.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  unfold pascalCenteredXiMellinQuadraticZeroMoment
    pascalCenteredXiMellinSecondDifferenceZeroMoment
  congr 1
  funext z
  exact (pascalCenteredXiMellinSecondDifferenceWeight_tau_zero_eq_quadraticWeight
    hε z).symm

/-! ## Gate F: arithmetic endpoint and its epsilon limit -/

/-- The inner `X → ∞` endpoint of the quadratic arithmetic approximants. -/
noncomputable def pascalCenteredXiMellinQuadraticArithmeticEndpoint
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℂ :=
  -(2 * Real.pi * Complex.I) *
    pascalCenteredXiMellinQuadraticZeroMoment ε W

/-- The quadratic arithmetic endpoint converges as `ε → 0+` to the fixed
centered Xi second-moment endpoint. -/
theorem tendsto_pascalCenteredXiMellinQuadraticArithmeticEndpoint_epsilon
    (W : PascalCenteredXiResidueTransportWindow) :
    Tendsto
      (fun ε : ℝ => pascalCenteredXiMellinQuadraticArithmeticEndpoint ε W)
      (𝓝[>] 0)
      (nhds (-(2 * Real.pi * Complex.I) *
        pascalCenteredXiZeroDiskSecondMoment W.R)) := by
  have hmoment := tendsto_pascalCenteredXiMellinQuadraticZeroMoment_epsilon W
  have hconst : Tendsto (fun _ : ℝ =>
      -(2 * Real.pi * Complex.I)) (𝓝[>] 0)
      (nhds (-(2 * Real.pi * Complex.I))) := tendsto_const_nhds
  simpa [pascalCenteredXiMellinQuadraticArithmeticEndpoint] using
    hconst.mul hmoment

/-! ## Gate G: fixed second contour endpoint -/

/-- The ordered arithmetic endpoint has the fixed second Xi outer-contour
mass as its `ε → 0+` target.  The identification uses the existing
boundary-safe contour theorem and performs no new contour calculation. -/
theorem tendsto_pascalCenteredXiMellinQuadraticArithmeticEndpoint_secondContour
    (W : PascalCenteredXiResidueTransportWindow) :
    Tendsto
      (fun ε : ℝ => pascalCenteredXiMellinQuadraticArithmeticEndpoint ε W)
      (𝓝[>] 0)
      (nhds (pascalCenteredXiSecondOuterContourMass W.R)) := by
  have hendpoint :=
    tendsto_pascalCenteredXiMellinQuadraticArithmeticEndpoint_epsilon W
  rw [pascalCenteredXiSecondOuterContourMass_eq_zeroDiskSecondMoment
    W.circle_safe]
  exact hendpoint

/-! ## Gate H: ordered iterated-limit certificate -/

/-- The ordered certificate: for every fixed `ε > 0`, first take `X → ∞`,
then send the resulting endpoint through `ε → 0+` to the fixed second contour
mass.  It does not assert the reverse order, a joint limit, uniformity in
`ε`, or any exchange of limits. -/
theorem pascalCenteredXiMellinQuadraticIteratedLimitCertificate
    (W : PascalCenteredXiResidueTransportWindow) :
    (∀ ε : ℝ, 0 < ε →
      Tendsto
        (fun X => pascalCenteredXiMellinQuadraticArithmeticApproximant ε W X)
        atTop
        (nhds (pascalCenteredXiMellinQuadraticArithmeticEndpoint ε W))) ∧
    Tendsto
      (fun ε : ℝ => pascalCenteredXiMellinQuadraticArithmeticEndpoint ε W)
      (𝓝[>] 0)
      (nhds (pascalCenteredXiSecondOuterContourMass W.R)) := by
  constructor
  · intro ε hε
    simpa [pascalCenteredXiMellinQuadraticArithmeticEndpoint] using
      (tendsto_pascalCenteredXiMellinQuadraticArithmeticApproximant hε W)
  · exact tendsto_pascalCenteredXiMellinQuadraticArithmeticEndpoint_secondContour W

end DkMath.RH.CFBRCProjection
