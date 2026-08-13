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

/-- Gate 3A scalar lift of the finite prime contribution.

This is deliberately only a scalar-layer lift of the normalized real
contribution.  It is not the original complex contour quantity; Gate 3B
below reconstructs that quantity from the source right-edge integral. -/
noncomputable def pascalCenteredXiMellinQuadraticPrimeVerticalBase
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℂ :=
  (pascalCenteredXiMellinQuadraticNormalizedPrimeContribution ε W X : ℂ) *
    (Real.pi : ℂ)

/-- Gate 3A scalar lift of the archimedean contribution; not a complex
contour source quantity. -/
noncomputable def pascalCenteredXiMellinQuadraticArchimedeanVerticalBase
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℂ :=
  (pascalCenteredXiMellinQuadraticNormalizedArchimedeanContribution ε W : ℂ) *
    (Real.pi : ℂ)

/-- Gate 3A scalar lift of the elementary contribution; not a complex
contour source quantity. -/
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

/-! ## Gate 3B.0: source-level complex reconstruction -/

/-- Remove the vertical path orientation from a genuine complex source
quantity.  This acts on the source integral itself, not on its real part. -/
noncomputable def pascalCenteredXiVerticalDeorient (z : ℂ) : ℂ :=
  -Complex.I * z

theorem pascalCenteredXiVerticalDeorient_re_eq_im (z : ℂ) :
    (pascalCenteredXiVerticalDeorient z).re = z.im := by
  simp [pascalCenteredXiVerticalDeorient, Complex.mul_re]

private theorem pascalCenteredXiVerticalDeorient_re_eq_pi_mul_normalized_re
    (z : ℂ) :
    (pascalCenteredXiVerticalDeorient z).re =
      Real.pi * ((2 * Real.pi * Complex.I)⁻¹ * (2 * z)).re := by
  unfold pascalCenteredXiVerticalDeorient
  simp only [Complex.mul_re, Complex.mul_im, Complex.inv_re, Complex.inv_im,
    Complex.normSq, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  norm_num
  field_simp [Real.pi_ne_zero]

private theorem pascalCenteredXiVerticalDeorient_add_re (a b c : ℂ) :
    (pascalCenteredXiVerticalDeorient (a + b + c)).re =
      (pascalCenteredXiVerticalDeorient a).re +
        (pascalCenteredXiVerticalDeorient b).re +
        (pascalCenteredXiVerticalDeorient c).re := by
  unfold pascalCenteredXiVerticalDeorient
  simp only [mul_add, Complex.add_re]

/-- Genuine oriented prime source surface before deorientation.  The `I` is
retained by `pascalPrimePowerRightEdgeCutoffIntegral`. -/
noncomputable def pascalCenteredXiMellinQuadraticOrientedPrimeSurface
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℂ :=
  pascalPrimePowerRightEdgeCutoffIntegral
    (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
    W.rectangle.σ W.rectangle.T X

/-- Genuine oriented archimedean source surface before deorientation. -/
noncomputable def pascalCenteredXiMellinQuadraticOrientedArchimedeanSurface
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℂ :=
  pascalXiArchimedeanRightEdgeIntegral
    (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
    W.rectangle.σ W.rectangle.T

/-- Genuine oriented elementary source surface before deorientation. -/
noncomputable def pascalCenteredXiMellinQuadraticOrientedElementarySurface
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℂ :=
  pascalXiElementaryRightEdgeIntegral
    (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
    W.rectangle.σ W.rectangle.T

/-- The genuine complex vertical surface, reconstructed from the three
source-level oriented right-edge integrals and deoriented once. -/
noncomputable def pascalCenteredXiMellinQuadraticComplexVerticalSurface
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℂ :=
  pascalCenteredXiVerticalDeorient
    (pascalCenteredXiMellinQuadraticOrientedPrimeSurface ε W X +
      pascalCenteredXiMellinQuadraticOrientedArchimedeanSurface ε W +
      pascalCenteredXiMellinQuadraticOrientedElementarySurface ε W)

/-- The genuine whole complex surface: the deoriented vertical source plus
the top horizontal source with its remaining `-I` orientation. -/
noncomputable def pascalCenteredXiMellinQuadraticComplexWholeSurface
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℂ :=
  pascalCenteredXiMellinQuadraticComplexVerticalSurface ε W X -
    Complex.I * pascalCenteredXiMellinQuadraticHorizontalBase ε W

theorem pascalCenteredXiMellinQuadraticOrientedPrimeSurface_deorient_re_eq_pi_mul_normalized
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    (pascalCenteredXiVerticalDeorient
      (pascalCenteredXiMellinQuadraticOrientedPrimeSurface ε W X)).re =
      Real.pi * pascalCenteredXiMellinQuadraticNormalizedPrimeContribution ε W X := by
  unfold pascalCenteredXiMellinQuadraticOrientedPrimeSurface
  rw [pascalPrimePowerRightEdgeCutoffIntegral_eq_vonMangoldt_sum
    (pascalCenteredXiMellinSecondDifferenceWeight_differentiable hε)
    W.rectangle.σ W.rectangle.T X]
  unfold pascalCenteredXiMellinQuadraticNormalizedPrimeContribution
  change (pascalCenteredXiVerticalDeorient _).re =
    Real.pi * (((2 * Real.pi * Complex.I)⁻¹ * _).re)
  exact pascalCenteredXiVerticalDeorient_re_eq_pi_mul_normalized_re _

theorem pascalCenteredXiMellinQuadraticOrientedArchimedeanSurface_deorient_re_eq_pi_mul_normalized
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) :
    (pascalCenteredXiVerticalDeorient
      (pascalCenteredXiMellinQuadraticOrientedArchimedeanSurface ε W)).re =
      Real.pi * pascalCenteredXiMellinQuadraticNormalizedArchimedeanContribution ε W := by
  unfold pascalCenteredXiVerticalDeorient
    pascalCenteredXiMellinQuadraticOrientedArchimedeanSurface
  change (pascalCenteredXiVerticalDeorient
    (pascalXiArchimedeanRightEdgeIntegral
      (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
      W.rectangle.σ W.rectangle.T)).re =
    Real.pi * ((2 * Real.pi * Complex.I)⁻¹ *
      (2 * pascalXiArchimedeanRightEdgeIntegral
        (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
        W.rectangle.σ W.rectangle.T)).re
  exact pascalCenteredXiVerticalDeorient_re_eq_pi_mul_normalized_re
    (pascalXiArchimedeanRightEdgeIntegral
      (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
      W.rectangle.σ W.rectangle.T)

theorem pascalCenteredXiMellinQuadraticOrientedElementarySurface_deorient_re_eq_pi_mul_normalized
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) :
    (pascalCenteredXiVerticalDeorient
      (pascalCenteredXiMellinQuadraticOrientedElementarySurface ε W)).re =
      Real.pi * pascalCenteredXiMellinQuadraticNormalizedElementaryContribution ε W := by
  unfold pascalCenteredXiVerticalDeorient
    pascalCenteredXiMellinQuadraticOrientedElementarySurface
  change (pascalCenteredXiVerticalDeorient
    (pascalXiElementaryRightEdgeIntegral
      (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
      W.rectangle.σ W.rectangle.T)).re =
    Real.pi * ((2 * Real.pi * Complex.I)⁻¹ *
      (2 * pascalXiElementaryRightEdgeIntegral
        (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
        W.rectangle.σ W.rectangle.T)).re
  exact pascalCenteredXiVerticalDeorient_re_eq_pi_mul_normalized_re
    (pascalXiElementaryRightEdgeIntegral
      (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
      W.rectangle.σ W.rectangle.T)

theorem pascalCenteredXiMellinQuadraticComplexWholeSurface_re_eq_scalarSurface
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    (pascalCenteredXiMellinQuadraticComplexWholeSurface ε W X).re =
      pascalCenteredXiMellinQuadraticScalarSurface ε W X := by
  unfold pascalCenteredXiMellinQuadraticComplexWholeSurface
    pascalCenteredXiMellinQuadraticComplexVerticalSurface
    pascalCenteredXiMellinQuadraticScalarSurface
    pascalCenteredXiMellinQuadraticVerticalBase
  have hde := pascalCenteredXiVerticalDeorient_add_re
    (pascalCenteredXiMellinQuadraticOrientedPrimeSurface ε W X)
    (pascalCenteredXiMellinQuadraticOrientedArchimedeanSurface ε W)
    (pascalCenteredXiMellinQuadraticOrientedElementarySurface ε W)
  simp only [Complex.sub_re]
  rw [hde]
  rw [pascalCenteredXiMellinQuadraticOrientedPrimeSurface_deorient_re_eq_pi_mul_normalized
      hε W X,
    pascalCenteredXiMellinQuadraticOrientedArchimedeanSurface_deorient_re_eq_pi_mul_normalized,
    pascalCenteredXiMellinQuadraticOrientedElementarySurface_deorient_re_eq_pi_mul_normalized]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, Complex.add_re,
    pascalCenteredXiMellinQuadraticPrimeVerticalBase,
    pascalCenteredXiMellinQuadraticArchimedeanVerticalBase,
    pascalCenteredXiMellinQuadraticElementaryVerticalBase,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem pascalCenteredXiMellinQuadraticScalarExcess_eq_complexWholeSurface_re_sub_radial
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinQuadraticScalarExcess ε W X =
      (pascalCenteredXiMellinQuadraticComplexWholeSurface ε W X).re -
        Real.pi * pascalCenteredXiFixedRadialSecondMomentFunctional W.R := by
  rw [pascalCenteredXiMellinQuadraticComplexWholeSurface_re_eq_scalarSurface hε W X]
  rfl

/-! ## Gate 3B.1a: pointwise source audit -/

/-- The pointwise prime source after applying the complex deorientation.
The finite cutoff and the original right-edge `I` remain visible. -/
noncomputable def pascalCenteredXiMellinQuadraticPrimeDeorientedIntegrand
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (t : ℝ) : ℂ :=
  pascalCenteredXiVerticalDeorient
    (pascalPrimePowerRightEdgeCutoffIntegrand
      (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
      W.rectangle.σ X t)

/-- The pointwise archimedean source after complex deorientation. -/
noncomputable def pascalCenteredXiMellinQuadraticArchimedeanDeorientedIntegrand
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (t : ℝ) : ℂ :=
  pascalCenteredXiVerticalDeorient
    (pascalXiArchimedeanRightEdgeIntegrand
      (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
      W.rectangle.σ t)

/-- The pointwise elementary source after complex deorientation. -/
noncomputable def pascalCenteredXiMellinQuadraticElementaryDeorientedIntegrand
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (t : ℝ) : ℂ :=
  pascalCenteredXiVerticalDeorient
    (pascalXiElementaryRightEdgeIntegrand
      (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
      W.rectangle.σ t)

/-- The pointwise deoriented vertical source, before interval integration. -/
noncomputable def pascalCenteredXiMellinQuadraticDeorientedVerticalIntegrand
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (t : ℝ) : ℂ :=
  pascalCenteredXiMellinQuadraticPrimeDeorientedIntegrand ε W X t +
    pascalCenteredXiMellinQuadraticArchimedeanDeorientedIntegrand ε W t +
    pascalCenteredXiMellinQuadraticElementaryDeorientedIntegrand ε W t

theorem pascalCenteredXiMellinQuadraticDeorientedVerticalIntegrand_eq_deorient_source
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (t : ℝ) :
    pascalCenteredXiMellinQuadraticDeorientedVerticalIntegrand ε W X t =
      pascalCenteredXiVerticalDeorient
        (pascalPrimePowerRightEdgeCutoffIntegrand
            (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
            W.rectangle.σ X t +
          pascalXiArchimedeanRightEdgeIntegrand
            (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
            W.rectangle.σ t +
          pascalXiElementaryRightEdgeIntegrand
            (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
            W.rectangle.σ t) := by
  simp only [pascalCenteredXiMellinQuadraticDeorientedVerticalIntegrand,
    pascalCenteredXiMellinQuadraticPrimeDeorientedIntegrand,
    pascalCenteredXiMellinQuadraticArchimedeanDeorientedIntegrand,
    pascalCenteredXiMellinQuadraticElementaryDeorientedIntegrand,
    pascalCenteredXiVerticalDeorient, mul_add, add_assoc]

/-- Finite interval lift of the deoriented prime source. -/
noncomputable def pascalCenteredXiMellinQuadraticPrimeDeorientedSurface
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℂ :=
  ∫ t in (-W.rectangle.T)..W.rectangle.T,
    pascalCenteredXiMellinQuadraticPrimeDeorientedIntegrand ε W X t

/-- Finite interval lift of the deoriented archimedean source. -/
noncomputable def pascalCenteredXiMellinQuadraticArchimedeanDeorientedSurface
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℂ :=
  ∫ t in (-W.rectangle.T)..W.rectangle.T,
    pascalCenteredXiMellinQuadraticArchimedeanDeorientedIntegrand ε W t

/-- Finite interval lift of the deoriented elementary source. -/
noncomputable def pascalCenteredXiMellinQuadraticElementaryDeorientedSurface
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℂ :=
  ∫ t in (-W.rectangle.T)..W.rectangle.T,
    pascalCenteredXiMellinQuadraticElementaryDeorientedIntegrand ε W t

theorem pascalCenteredXiMellinQuadraticDeorientedSurfaces_eq_complexVerticalSurface
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinQuadraticPrimeDeorientedSurface ε W X +
        pascalCenteredXiMellinQuadraticArchimedeanDeorientedSurface ε W +
      pascalCenteredXiMellinQuadraticElementaryDeorientedSurface ε W =
      pascalCenteredXiMellinQuadraticComplexVerticalSurface ε W X := by
  unfold pascalCenteredXiMellinQuadraticPrimeDeorientedSurface
    pascalCenteredXiMellinQuadraticArchimedeanDeorientedSurface
    pascalCenteredXiMellinQuadraticElementaryDeorientedSurface
    pascalCenteredXiMellinQuadraticPrimeDeorientedIntegrand
    pascalCenteredXiMellinQuadraticArchimedeanDeorientedIntegrand
    pascalCenteredXiMellinQuadraticElementaryDeorientedIntegrand
    pascalCenteredXiMellinQuadraticComplexVerticalSurface
    pascalCenteredXiMellinQuadraticOrientedPrimeSurface
    pascalCenteredXiMellinQuadraticOrientedArchimedeanSurface
    pascalCenteredXiMellinQuadraticOrientedElementarySurface
    pascalCenteredXiVerticalDeorient
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  rw [mul_add, mul_add]
  rfl

/-! ## Gate 3B.1b: explicit radial comparison -/

/-- The scalar radial comparison carried by the current finite excess. -/
noncomputable def pascalCenteredXiMellinQuadraticRadialComparison
    (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  Real.pi * pascalCenteredXiFixedRadialSecondMomentFunctional W.R

theorem pascalCenteredXiMellinQuadraticScalarExcess_eq_complexWholeSurface_re_sub_radialComparison
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinQuadraticScalarExcess ε W X =
      (pascalCenteredXiMellinQuadraticComplexWholeSurface ε W X).re -
        pascalCenteredXiMellinQuadraticRadialComparison W := by
  rw [pascalCenteredXiMellinQuadraticScalarExcess_eq_complexWholeSurface_re_sub_radial
    hε W X]
  rfl

/-! Gate 3B.1c remains an explicit obstruction boundary: this module supplies
no positive energy provider.  The source reconstruction and radial comparison
do not by themselves yield a square, Gram form, or nonnegativity theorem for
the finite scalar excess. -/

end DkMath.RH.CFBRCProjection
