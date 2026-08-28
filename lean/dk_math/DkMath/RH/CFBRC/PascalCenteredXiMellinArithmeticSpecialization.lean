/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiFiniteArithmeticExplicitFormula
import DkMath.RH.CFBRC.PascalCenteredXiExplicitFormulaHorizontalPairing
import Mathlib.Tactic

/-!
# Fixed Mellin second-difference arithmetic specialization

This module specializes the generic finite arithmetic explicit formula of
XDP-018 to the canonical compact multiplicative box
`centeredMellinBoxApprox ε`.  The parameters `ε > 0`, `τ`, the residue window,
and the height remain fixed in every principal theorem.

The box support, continuity, differentiability, and evenness obligations are
discharged by the existing Mellin API.  The `τ = 0` branch is the patched
quadratic-Mellin value from `centeredMellinSecondDifferenceWeight`; it is not
the zero function and it is not the unweighted quadratic `z ^ 2` function.
No Mellin limit, arithmetic-cutoff limit exchange, horizontal-term
disappearance, defect statement, or RH consequence is asserted here.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open Filter

/-! ## Gate A: canonical weight and admissibility -/

/-- The canonical centered Mellin second-difference weight used by the Pascal
finite arithmetic surface for fixed box width `ε` and dilation parameter `τ`.

The underlying definition retains its patched `τ = 0` branch. -/
noncomputable def pascalCenteredXiMellinSecondDifferenceWeight
    (ε τ : ℝ) : ℂ → ℂ :=
  centeredMellinSecondDifferenceWeight
    (centeredMellinBoxApprox ε) τ

/-- Positive box width makes the canonical Mellin second-difference weight
entire in the centered complex variable. -/
theorem pascalCenteredXiMellinSecondDifferenceWeight_differentiable
    {ε τ : ℝ} (hε : 0 < ε) :
    Differentiable ℂ
      (pascalCenteredXiMellinSecondDifferenceWeight ε τ) := by
  unfold pascalCenteredXiMellinSecondDifferenceWeight
  exact differentiable_centeredMellinSecondDifferenceWeight
    (Real.exp_pos (-ε))
    (centeredMellinBoxApprox_endpoints_ordered hε)
    (centeredMellinBoxApprox_support_subset hε)
    (centeredMellinBoxApprox_continuousOn hε)

/-- The canonical Mellin second-difference weight is even in the centered
complex coordinate, including the patched `τ = 0` branch. -/
theorem pascalCenteredXiMellinSecondDifferenceWeight_even
    {ε τ : ℝ} (hε : 0 < ε) :
    PascalCenteredEvenWeight
      (pascalCenteredXiMellinSecondDifferenceWeight ε τ) := by
  unfold pascalCenteredXiMellinSecondDifferenceWeight
  exact centeredMellinSecondDifferenceWeight_centeredMellinBoxApprox_even hε

/-! ## Gate B: named specialized zero-side observable -/

/-- The finite fixed-Xi zero-disk moment for the canonical Mellin weight. -/
noncomputable def pascalCenteredXiMellinSecondDifferenceZeroMoment
    (ε τ : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℂ :=
  pascalCenteredXiZeroDiskWeightedMoment
    (pascalCenteredXiMellinSecondDifferenceWeight ε τ) W.R

/-! ## Gate C: fixed Mellin four-term identity -/

/-- The exact finite four-term right-edge identity for the canonical Mellin
second-difference weight.

All four terms use the same specialized weight.  The top-horizontal term is
retained at the fixed finite rectangle height. -/
theorem pascalCenteredXiMellinFiniteExplicitFormula
    {ε τ : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    -(2 * Real.pi * Complex.I) *
        pascalCenteredXiMellinSecondDifferenceZeroMoment ε τ W =
      2 * pascalXiOrdinaryZetaRightEdgeIntegral
          (pascalCenteredXiMellinSecondDifferenceWeight ε τ)
          W.rectangle.σ W.rectangle.T +
      2 * pascalXiArchimedeanRightEdgeIntegral
          (pascalCenteredXiMellinSecondDifferenceWeight ε τ)
          W.rectangle.σ W.rectangle.T +
      2 * pascalXiElementaryRightEdgeIntegral
          (pascalCenteredXiMellinSecondDifferenceWeight ε τ)
          W.rectangle.σ W.rectangle.T +
      2 * pascalCenteredXiTopHorizontalContribution
          (pascalCenteredXiMellinSecondDifferenceWeight ε τ)
          W.toContourTransportWindow := by
  exact pascalCenteredXiFiniteExplicitFormula_eq_zeta_archimedean_elementary_top
    (pascalCenteredXiMellinSecondDifferenceWeight_differentiable hε)
    (pascalCenteredXiMellinSecondDifferenceWeight_even hε) W

/-! ## Gate D: specialized arithmetic approximant -/

/-- The finite Pascal/von Mangoldt approximant for fixed Mellin parameters. -/
noncomputable def pascalCenteredXiMellinFiniteArithmeticApproximant
    (ε τ : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℂ :=
  pascalCenteredXiFiniteArithmeticApproximant
    (pascalCenteredXiMellinSecondDifferenceWeight ε τ) W X

/-! ## Gate E: fixed Mellin arithmetic convergence -/

/-- For every fixed `ε > 0`, `τ`, and finite residue window, the specialized
arithmetic approximants converge as `X → ∞` to the same specialized finite-Xi
zero-moment endpoint.  No condition `τ ≠ 0` is needed. -/
theorem tendsto_pascalCenteredXiMellinFiniteArithmeticExplicitFormula
    {ε τ : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    Tendsto
      (fun X => pascalCenteredXiMellinFiniteArithmeticApproximant ε τ W X)
      atTop
      (nhds (-(2 * Real.pi * Complex.I) *
        pascalCenteredXiMellinSecondDifferenceZeroMoment ε τ W)) := by
  exact tendsto_pascalCenteredXiFiniteArithmeticExplicitFormula
    (pascalCenteredXiMellinSecondDifferenceWeight_differentiable hε)
    (pascalCenteredXiMellinSecondDifferenceWeight_even hε) W

/-! ## Gate F: finite von Mangoldt surface -/

/-- The specialized finite arithmetic approximant expanded as a finite
von Mangoldt kernel sum plus the archimedean, elementary, and top terms. -/
theorem pascalCenteredXiMellinFiniteArithmeticApproximant_eq_vonMangoldt_sum
    {ε τ : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinFiniteArithmeticApproximant ε τ W X =
      2 * (∑ n ∈ Finset.range (X + 1),
        ∫ t in (-W.rectangle.T)..W.rectangle.T,
          (pascalCenteredXiMellinSecondDifferenceWeight ε τ
            (pascalOrdinaryToCentered
              (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
            ((ArithmeticFunction.vonMangoldt n : ℂ) *
              ((n : ℂ) ^
                (-(pascalSymmetricRectangleRightEdge W.rectangle.σ t)))) *
            Complex.I)) +
      2 * pascalXiArchimedeanRightEdgeIntegral
        (pascalCenteredXiMellinSecondDifferenceWeight ε τ)
        W.rectangle.σ W.rectangle.T +
      2 * pascalXiElementaryRightEdgeIntegral
        (pascalCenteredXiMellinSecondDifferenceWeight ε τ)
        W.rectangle.σ W.rectangle.T +
      2 * pascalCenteredXiTopHorizontalContribution
        (pascalCenteredXiMellinSecondDifferenceWeight ε τ)
        W.toContourTransportWindow := by
  exact pascalCenteredXiFiniteArithmeticApproximant_eq_vonMangoldt_sum
    (pascalCenteredXiMellinSecondDifferenceWeight_differentiable hε) W X

/-! ## Gate G: nonzero-τ kernel surface -/

/-- For `τ ≠ 0`, expose the exact exponential symmetric second-difference
kernel of the specialized Mellin weight.  This theorem is intentionally
separate from the all-`τ` arithmetic convergence theorem. -/
theorem pascalCenteredXiMellinSecondDifferenceWeight_eq_kernel_mul
    {ε τ : ℝ} (hτ : τ ≠ 0) (z : ℂ) :
    pascalCenteredXiMellinSecondDifferenceWeight ε τ z =
      ((Complex.exp ((τ : ℂ) * z) - 2 +
          Complex.exp (-(τ : ℂ) * z)) /
        (τ : ℂ) ^ 2) *
      centeredMellinSpectralWeight
        (centeredMellinBoxApprox ε) z := by
  unfold pascalCenteredXiMellinSecondDifferenceWeight
  exact centeredMellinSecondDifferenceWeight_eq_kernel_mul hτ

/-! ## Gate H: patched `τ = 0` surface -/

/-- At `τ = 0`, the canonical weight is the quadratic multiplier times the
box Mellin spectral weight.  This is not a zero-function statement and does
not identify the spectral weight with `1`. -/
theorem pascalCenteredXiMellinSecondDifferenceWeight_tau_zero_eq_quadraticWeight
    {ε : ℝ} (_hε : 0 < ε) (z : ℂ) :
    pascalCenteredXiMellinSecondDifferenceWeight ε 0 z =
      z ^ 2 * centeredMellinSpectralWeight
        (centeredMellinBoxApprox ε) z := by
  simp [pascalCenteredXiMellinSecondDifferenceWeight,
    centeredMellinSecondDifferenceWeight]

end DkMath.RH.CFBRCProjection
