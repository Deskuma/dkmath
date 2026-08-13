/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideSignAudit
import Mathlib.Tactic

/-!
# Whole-surface orientation and excess audit

Gate 3A removes the opaque `(2 * π * I)⁻¹` from the finite arithmetic
surface.  The three right-edge terms carry a vertical `I` and therefore
contribute their real parts divided by `π`; the top-horizontal term has the
other orientation and contributes its imaginary part divided by `π`.

This is an algebraic representation layer.  It introduces no square identity,
nonnegativity provider, defect sign theorem, RH consequence, or height limit.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology Interval

/-! ## Gate 3A.1: orientation-normalized vertical bases -/

/-- The finite prime right-edge base with its path-orientation `I` removed. -/
noncomputable def pascalCenteredXiMellinQuadraticPrimeVerticalBase
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℂ :=
  (pascalCenteredXiMellinQuadraticNormalizedPrimeContribution ε W X : ℂ) *
    (Real.pi : ℂ)

/-- The archimedean right-edge base with its path-orientation `I` removed. -/
noncomputable def pascalCenteredXiMellinQuadraticArchimedeanVerticalBase
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℂ :=
  (pascalCenteredXiMellinQuadraticNormalizedArchimedeanContribution ε W : ℂ) *
    (Real.pi : ℂ)

/-- The elementary right-edge base with its path-orientation `I` removed. -/
noncomputable def pascalCenteredXiMellinQuadraticElementaryVerticalBase
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℂ :=
  (pascalCenteredXiMellinQuadraticNormalizedElementaryContribution ε W : ℂ) *
    (Real.pi : ℂ)

/-- The complete vertical base is the sum of the three right-edge bases. -/
noncomputable def pascalCenteredXiMellinQuadraticVerticalBase
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℂ :=
  pascalCenteredXiMellinQuadraticPrimeVerticalBase ε W X +
    pascalCenteredXiMellinQuadraticArchimedeanVerticalBase ε W +
    pascalCenteredXiMellinQuadraticElementaryVerticalBase ε W

/-! ## Gate 3A.2: scalar orientation identities -/

private theorem normalized_vertical_re_eq_re_div_pi (z : ℂ) :
    ((2 * Real.pi * Complex.I)⁻¹ * (2 * (z * Complex.I))).re =
      z.re / Real.pi := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.inv_re, Complex.inv_im,
    Complex.normSq, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  norm_num
  field_simp [Real.pi_ne_zero]

private theorem normalized_horizontal_re_eq_im_div_pi (z : ℂ) :
    ((2 * Real.pi * Complex.I)⁻¹ * (2 * z)).re =
      z.im / Real.pi := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.inv_re, Complex.inv_im,
    Complex.normSq, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  norm_num
  field_simp [Real.pi_ne_zero]

/-! ## Gate 3A.3: contribution orientation theorems -/

theorem pascalCenteredXiMellinQuadraticNormalizedPrimeContribution_eq_re_div_pi
    {ε : ℝ} (_hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinQuadraticNormalizedPrimeContribution ε W X =
      (pascalCenteredXiMellinQuadraticPrimeVerticalBase ε W X).re /
        Real.pi := by
  simp [pascalCenteredXiMellinQuadraticPrimeVerticalBase,
    Complex.ofReal_re, Complex.ofReal_im]

theorem pascalCenteredXiMellinQuadraticNormalizedArchimedeanContribution_eq_re_div_pi
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) :
    pascalCenteredXiMellinQuadraticNormalizedArchimedeanContribution ε W =
      (pascalCenteredXiMellinQuadraticArchimedeanVerticalBase ε W).re /
        Real.pi := by
  simp [pascalCenteredXiMellinQuadraticArchimedeanVerticalBase,
    Complex.ofReal_re, Complex.ofReal_im]

theorem pascalCenteredXiMellinQuadraticNormalizedElementaryContribution_eq_re_div_pi
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) :
    pascalCenteredXiMellinQuadraticNormalizedElementaryContribution ε W =
      (pascalCenteredXiMellinQuadraticElementaryVerticalBase ε W).re /
        Real.pi := by
  simp [pascalCenteredXiMellinQuadraticElementaryVerticalBase,
    Complex.ofReal_re, Complex.ofReal_im]

theorem pascalCenteredXiMellinQuadraticNormalizedTopContribution_eq_im_div_pi
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) :
    pascalCenteredXiMellinQuadraticNormalizedTopContribution ε W =
      (pascalCenteredXiTopHorizontalContribution
        (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
        W.toContourTransportWindow).im / Real.pi := by
  unfold pascalCenteredXiMellinQuadraticNormalizedTopContribution
  change ((2 * Real.pi * Complex.I)⁻¹ * (2 * _)).re = _
  exact normalized_horizontal_re_eq_im_div_pi _

/-! ## Gate 3A.4: scalar surface and excess -/

/-- The finite top-horizontal base, kept separate from the vertical base. -/
noncomputable def pascalCenteredXiMellinQuadraticHorizontalBase
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℂ :=
  pascalCenteredXiTopHorizontalContribution
    (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
    W.toContourTransportWindow

/-- The unnormalized scalar carried by the whole finite arithmetic surface. -/
noncomputable def pascalCenteredXiMellinQuadraticScalarSurface
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℝ :=
  (pascalCenteredXiMellinQuadraticVerticalBase ε W X).re +
    (pascalCenteredXiMellinQuadraticHorizontalBase ε W).im

/-- The normalized real arithmetic surface is the scalar surface divided by π.
The prime, both corrections, and the top-horizontal term are all retained.
-/
theorem pascalCenteredXiMellinQuadraticNormalizedArithmeticApproximant_re_eq_scalarSurface_div_pi
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    (pascalCenteredXiMellinQuadraticNormalizedArithmeticApproximant ε W X).re =
      pascalCenteredXiMellinQuadraticScalarSurface ε W X / Real.pi := by
  rw [pascalCenteredXiMellinQuadraticNormalizedArithmeticApproximant_re_eq_four_terms
    hε W X,
    pascalCenteredXiMellinQuadraticNormalizedPrimeContribution_eq_re_div_pi hε W X,
    pascalCenteredXiMellinQuadraticNormalizedArchimedeanContribution_eq_re_div_pi,
    pascalCenteredXiMellinQuadraticNormalizedElementaryContribution_eq_re_div_pi,
    pascalCenteredXiMellinQuadraticNormalizedTopContribution_eq_im_div_pi]
  unfold pascalCenteredXiMellinQuadraticScalarSurface
    pascalCenteredXiMellinQuadraticVerticalBase
    pascalCenteredXiMellinQuadraticHorizontalBase
  simp only [Complex.add_re]
  field_simp [Real.pi_ne_zero]

/-- The prime-side scalar excess over the radial mass. -/
noncomputable def pascalCenteredXiMellinQuadraticScalarExcess
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℝ :=
  pascalCenteredXiMellinQuadraticScalarSurface ε W X -
    Real.pi * pascalCenteredXiFixedRadialSecondMomentFunctional W.R

/-- The scalar excess is exactly `-π` times the finite arithmetic defect. -/
theorem pascalCenteredXiMellinQuadraticScalarExcess_eq_neg_pi_mul_defect
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinQuadraticScalarExcess ε W X =
      -Real.pi *
        pascalCenteredXiMellinQuadraticArithmeticDefectApproximant ε W X := by
  have hsurface :=
    pascalCenteredXiMellinQuadraticNormalizedArithmeticApproximant_re_eq_scalarSurface_div_pi
      hε W X
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hscalar :
      pascalCenteredXiMellinQuadraticScalarSurface ε W X =
        Real.pi *
          (pascalCenteredXiMellinQuadraticNormalizedArithmeticApproximant ε W X).re := by
    rw [hsurface]
    field_simp [hpi]
  change pascalCenteredXiMellinQuadraticScalarSurface ε W X -
      Real.pi * pascalCenteredXiFixedRadialSecondMomentFunctional W.R =
    -Real.pi *
      (pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
        (pascalCenteredXiMellinQuadraticNormalizedArithmeticApproximant ε W X).re)
  rw [hscalar]
  ring

/-- The excess is nonnegative exactly when the finite defect is nonpositive.
This equivalence is algebraic and is not itself a sign theorem. -/
theorem pascalCenteredXiMellinQuadraticScalarExcess_nonneg_iff_defect_nonpos
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    0 ≤ pascalCenteredXiMellinQuadraticScalarExcess ε W X ↔
      pascalCenteredXiMellinQuadraticArithmeticDefectApproximant ε W X ≤ 0 := by
  rw [pascalCenteredXiMellinQuadraticScalarExcess_eq_neg_pi_mul_defect hε W X]
  have hpi : 0 < Real.pi := Real.pi_pos
  constructor <;> intro h <;> nlinarith

end DkMath.RH.CFBRCProjection
