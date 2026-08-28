/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideUpperEnvelopeStrengthAudit

/-!
# CS10: finite prime-side source cancellation audit

This module returns to the finite arithmetic source after the CS9 strength
classification.  It names the prime cutoff residual, proves the exact
four-term cancellation against the finite Xi endpoint, and transports the
already authorized fixed-`ε` cutoff convergence to that residual.

The remaining signed residual is recorded as a source frontier.  No fixed-`ε`
sign theorem, limit exchange, or RH consequence is introduced.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-! ## CS10-A: the prime cutoff residual -/

/-- The single complex prime cutoff residual left after the finite correction
surfaces are removed. -/
noncomputable def pascalCenteredXiPrimeSideFiniteCutoffResidual
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℂ :=
  pascalCenteredXiPrimeSideQuadraticizationPrimeModeSum ε W X -
    pascalXiOrdinaryZetaRightEdgeIntegral
      (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
      W.rectangle.σ W.rectangle.T

/-- The prime-mode sum is exactly the existing XDP-017 finite right-edge
cutoff integral. -/
theorem pascalCenteredXiPrimeSideQuadraticizationPrimeModeSum_eq_cutoffIntegral
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideQuadraticizationPrimeModeSum ε W X =
      pascalPrimePowerRightEdgeCutoffIntegral
        (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
        W.rectangle.σ W.rectangle.T X := by
  unfold pascalCenteredXiPrimeSideQuadraticizationPrimeModeSum
    pascalCenteredXiPrimeSideQuadraticizationPrimeMode
  symm
  exact pascalPrimePowerRightEdgeCutoffIntegral_eq_vonMangoldt_sum
    (pascalCenteredXiMellinSecondDifferenceWeight_differentiable hε)
    W.rectangle.σ W.rectangle.T X

/-! ## CS10-B: exact correction cancellation -/

/-- The finite arithmetic approximant minus the exact finite Xi endpoint is
exactly twice the named prime cutoff residual.  The archimedean, elementary,
and top-horizontal terms cancel algebraically; none is estimated here. -/
theorem pascalCenteredXiMellinQuadraticArithmeticApproximant_sub_endpoint_eq_two_mul_primeResidual
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinQuadraticArithmeticApproximant ε W X -
        pascalCenteredXiMellinQuadraticArithmeticEndpoint ε W =
      2 * pascalCenteredXiPrimeSideFiniteCutoffResidual ε W X := by
  unfold pascalCenteredXiMellinQuadraticArithmeticApproximant
    pascalCenteredXiMellinQuadraticArithmeticEndpoint
  rw [pascalCenteredXiPrimeSideQuadraticization_source_ledger hε W X,
    pascalCenteredXiMellinQuadraticFiniteExplicitFormula hε W]
  unfold pascalCenteredXiPrimeSideFiniteCutoffResidual
  ring

/-! ## CS10-C: fixed-epsilon residual convergence -/

/-- For each fixed positive `ε`, the prime cutoff residual tends to zero as
`X → ∞`.  This is only the existing inner cutoff limit. -/
theorem tendsto_pascalCenteredXiPrimeSideFiniteCutoffResidual
    {ε : ℝ} (hε : 0 < ε)
  (W : PascalCenteredXiResidueTransportWindow) :
  Tendsto
      (fun X => pascalCenteredXiPrimeSideFiniteCutoffResidual ε W X)
      atTop (nhds 0) := by
  have hcut :=
    tendsto_pascalPrimePowerRightEdgeCutoffIntegral_of_residueTransportWindow
      (h := pascalCenteredXiMellinSecondDifferenceWeight ε 0)
      (pascalCenteredXiMellinSecondDifferenceWeight_differentiable hε) W
  have hsum (X : ℕ) :=
    pascalCenteredXiPrimeSideQuadraticizationPrimeModeSum_eq_cutoffIntegral hε W X
  change Tendsto
    (fun X => pascalCenteredXiPrimeSideQuadraticizationPrimeModeSum ε W X -
      pascalXiOrdinaryZetaRightEdgeIntegral
        (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
        W.rectangle.σ W.rectangle.T)
    atTop (nhds 0)
  simp_rw [hsum]
  simpa using hcut.sub (tendsto_const_nhds :
    Tendsto (fun _ : ℕ =>
      pascalXiOrdinaryZetaRightEdgeIntegral
        (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
        W.rectangle.σ W.rectangle.T) atTop
      (nhds (pascalXiOrdinaryZetaRightEdgeIntegral
        (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
        W.rectangle.σ W.rectangle.T)))

/-! ## CS10-D: the signed normalized coordinate -/

private theorem normalized_re_sub_normalized_re_eq_im_sub_div_two_pi
    (a b : ℂ) :
    ((2 * Real.pi * Complex.I : ℂ)⁻¹ * a).re -
        ((2 * Real.pi * Complex.I : ℂ)⁻¹ * b).re =
      (a - b).im / (2 * Real.pi) := by
  rw [← Complex.sub_re, ← mul_sub]
  simp only [Complex.mul_re, Complex.inv_re, Complex.inv_im,
    Complex.normSq, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  norm_num
  field_simp [Real.pi_ne_zero]

/-- The finite defect error sees only the signed imaginary coordinate of the
prime residual, with the normalization fixed by `(2 * π * I)⁻¹`. -/
theorem pascalCenteredXiMellinQuadraticArithmeticDefectApproximant_sub_endpoint_eq_neg_primeResidual_im_div_pi
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinQuadraticArithmeticDefectApproximant ε W X -
        pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint ε W =
      -(pascalCenteredXiPrimeSideFiniteCutoffResidual ε W X).im / Real.pi := by
  unfold pascalCenteredXiMellinQuadraticArithmeticDefectApproximant
    pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint
    pascalCenteredXiMellinQuadraticNormalizedArithmeticApproximant
    pascalCenteredXiMellinQuadraticNormalizedArithmeticEndpoint
  have hnorm :=
    normalized_re_sub_normalized_re_eq_im_sub_div_two_pi
      (pascalCenteredXiMellinQuadraticArithmeticApproximant ε W X)
      (pascalCenteredXiMellinQuadraticArithmeticEndpoint ε W)
  have hcancel :=
    pascalCenteredXiMellinQuadraticArithmeticApproximant_sub_endpoint_eq_two_mul_primeResidual
      hε W X
  calc
    (pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
        ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
          pascalCenteredXiMellinQuadraticArithmeticApproximant ε W X).re) -
        (pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
          ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
            pascalCenteredXiMellinQuadraticArithmeticEndpoint ε W).re) =
        -(((2 * Real.pi * Complex.I : ℂ)⁻¹ *
          pascalCenteredXiMellinQuadraticArithmeticApproximant ε W X).re -
          ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
            pascalCenteredXiMellinQuadraticArithmeticEndpoint ε W).re) := by ring
    _ = -(pascalCenteredXiMellinQuadraticArithmeticApproximant ε W X -
        pascalCenteredXiMellinQuadraticArithmeticEndpoint ε W).im /
          (2 * Real.pi) := by
      rw [hnorm]
      ring
    _ = -(pascalCenteredXiPrimeSideFiniteCutoffResidual ε W X).im /
          Real.pi := by
      rw [hcancel]
      unfold pascalCenteredXiPrimeSideFiniteCutoffResidual
      simp [Complex.mul_im]
      ring

/-! ## CS10-E--G: tail and signed-provider frontier -/

/-- The residual is already expressed through the finite von Mangoldt source
by the cutoff adapter.  Any infinite-tail representation would require a
separate sum/integral interchange certificate and is not asserted here. -/
inductive PascalCenteredXiPrimeSideFiniteCutoffSignedResidualGap : Prop
  | noIndependentSignedPrimeResidualProvider :
      PascalCenteredXiPrimeSideFiniteCutoffSignedResidualGap

end DkMath.RH.CFBRCProjection
