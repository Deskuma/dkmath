/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideGoodCutoffCofinalAnchorAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideQuadraticizationAudit
import Mathlib.Tactic

/-!
# CS22: cofinal radial-contact closure

This module identifies the CS21 cofinal arithmetic upper-anchor contract with
the weakest cofinal form of the existing finite radial comparison. Every
comparison in this file is finite algebra or a fixed-`ε` cofinality adapter.
The cofinal radial-contact provider remains an explicit frontier.

No universal finite sign, infinite exchange, endpoint sign, RH conclusion, or
independent prime-side provider is asserted here.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

local notation "DεX" => pascalCenteredXiMellinQuadraticArithmeticDefectApproximant
local notation "Dε∞" => pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint

/-! ## CS22-A: finite radial-contact deficit -/

/-- The finite radial comparison deficit, in geometric scalar units. -/
noncomputable def pascalCenteredXiPrimeSideFiniteRadialContactDeficit
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) : ℝ :=
  Real.pi * pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
    pascalCenteredXiMellinQuadraticScalarSurface ε W X

theorem pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_pi_mul_defect
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X =
      Real.pi * DεX ε W X := by
  have hsurface :=
    pascalCenteredXiPrimeSideQuadraticization_scalarSurface_eq_pi_mul_normalizedArithmetic_re
      hε W X
  unfold pascalCenteredXiPrimeSideFiniteRadialContactDeficit
    pascalCenteredXiMellinQuadraticArithmeticDefectApproximant
  rw [hsurface]
  ring

/-! ## CS22-B: pointwise radial-contact adapters -/

theorem pascalCenteredXiPrimeSideFiniteRadialContactDeficit_le_iff_defect_le
    {ε r : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    DεX ε W X ≤ r ↔
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X ≤ Real.pi * r := by
  have hEq := pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_pi_mul_defect
    hε W X
  constructor
  · intro h
    rw [hEq]
    exact mul_le_mul_of_nonneg_left h Real.pi_pos.le
  · intro h
    have hscaled : Real.pi * DεX ε W X ≤ Real.pi * r := by
      rw [← hEq]
      exact h
    exact le_of_mul_le_mul_left hscaled Real.pi_pos

theorem pascalCenteredXiPrimeSideFiniteRadialContactDeficit_le_iff_scalarSurface_ge
    {ε r : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    DεX ε W X ≤ r ↔
      Real.pi *
          (pascalCenteredXiFixedRadialSecondMomentFunctional W.R - r) ≤
        pascalCenteredXiMellinQuadraticScalarSurface ε W X := by
  rw [pascalCenteredXiPrimeSideFiniteRadialContactDeficit_le_iff_defect_le hε W X]
  unfold pascalCenteredXiPrimeSideFiniteRadialContactDeficit
  constructor <;> intro h <;> linarith

theorem pascalCenteredXiPrimeSideFiniteRadialContactDeficit_le_zero_iff
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    DεX ε W X ≤ 0 ↔
      Real.pi * pascalCenteredXiFixedRadialSecondMomentFunctional W.R ≤
        pascalCenteredXiMellinQuadraticScalarSurface ε W X := by
  simpa using
    (pascalCenteredXiPrimeSideFiniteRadialContactDeficit_le_iff_scalarSurface_ge
      (r := 0) hε W X)

/-! ## CS22-C/D: cofinal radial-contact contract -/

/-- Arbitrarily late finite radial surfaces may approach a target from above
up to any prescribed positive geometric tolerance. -/
def PascalCenteredXiPrimeSideCofinalRadialContactAt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (R : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ N : ℕ, ∃ X : ℕ, N ≤ X ∧
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X ≤ R + η

theorem pascalCenteredXiPrimeSideCofinalFiniteUpperAnchorAt_iff_cofinalRadialContactAt
    {ε r : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    PascalCenteredXiPrimeSideCofinalFiniteUpperAnchorAt ε W r ↔
      PascalCenteredXiPrimeSideCofinalRadialContactAt ε W (Real.pi * r) := by
  constructor
  · intro hanchor η hη N
    have hδ : 0 < η / Real.pi := div_pos hη Real.pi_pos
    rcases hanchor (η / Real.pi) hδ N with ⟨X, hNX, hupper⟩
    refine ⟨X, hNX, ?_⟩
    have hEq := pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_pi_mul_defect
      hε W X
    calc
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X =
          Real.pi * DεX ε W X := hEq
      _ ≤ Real.pi * (r + η / Real.pi) :=
        mul_le_mul_of_nonneg_left hupper Real.pi_pos.le
      _ = Real.pi * r + η := by
        field_simp [Real.pi_ne_zero]
  · intro hcontact δ hδ N
    have hη : 0 < Real.pi * δ := mul_pos Real.pi_pos hδ
    rcases hcontact (Real.pi * δ) hη N with ⟨X, hNX, hcontactX⟩
    refine ⟨X, hNX, ?_⟩
    have hscaled : Real.pi * DεX ε W X ≤ Real.pi * (r + δ) := by
      calc
      Real.pi * DεX ε W X =
          pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X :=
        (pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_pi_mul_defect
          hε W X).symm
      _ ≤ Real.pi * r + Real.pi * δ := hcontactX
      _ = Real.pi * (r + δ) := by ring
    exact le_of_mul_le_mul_left hscaled Real.pi_pos

/-- The zero-target form of cofinal radial contact. -/
def PascalCenteredXiPrimeSideCofinalRadialContactZeroAt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : Prop :=
  PascalCenteredXiPrimeSideCofinalRadialContactAt ε W 0

theorem pascalCenteredXiPrimeSideCofinalRadialContactZeroAt_iff_anchor_zero
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    PascalCenteredXiPrimeSideCofinalRadialContactZeroAt ε W ↔
      PascalCenteredXiPrimeSideCofinalFiniteUpperAnchorAt ε W 0 := by
  simpa [PascalCenteredXiPrimeSideCofinalRadialContactZeroAt] using
    (pascalCenteredXiPrimeSideCofinalFiniteUpperAnchorAt_iff_cofinalRadialContactAt
      (r := 0) hε W).symm

/-! ## CS22-E: endpoint strength classification -/

theorem pascalCenteredXiPrimeSideCofinalRadialContactAt_iff_endpoint_le
    {ε r : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    PascalCenteredXiPrimeSideCofinalRadialContactAt ε W (Real.pi * r) ↔
      Dε∞ ε W ≤ r := by
  constructor
  · intro hcontact
    apply (pascalCenteredXiPrimeSideCofinalFiniteUpperAnchorAt_iff_endpoint_le
      hε W).mp
    exact
      (pascalCenteredXiPrimeSideCofinalFiniteUpperAnchorAt_iff_cofinalRadialContactAt
        hε W).mpr hcontact
  · intro hend
    apply
      (pascalCenteredXiPrimeSideCofinalFiniteUpperAnchorAt_iff_cofinalRadialContactAt
        hε W).mp
    exact
      (pascalCenteredXiPrimeSideCofinalFiniteUpperAnchorAt_iff_endpoint_le
        hε W).mpr hend

theorem pascalCenteredXiPrimeSideCofinalRadialContactZeroAt_iff_endpoint_nonpos
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    PascalCenteredXiPrimeSideCofinalRadialContactZeroAt ε W ↔
      Dε∞ ε W ≤ 0 := by
  simpa [PascalCenteredXiPrimeSideCofinalRadialContactZeroAt] using
    (pascalCenteredXiPrimeSideCofinalRadialContactAt_iff_endpoint_le
      (r := 0) hε W)

/-! ## CS22-F: vanishing radial-contact family adapter -/

theorem pascalCenteredXiPrimeSideVanishingCofinalRadialContact_implies_upperEnvelope
    (W : PascalCenteredXiResidueTransportWindow)
    (r : ℝ → ℝ)
    (hr : Tendsto r (𝓝[>] 0) (nhds 0))
    (hcontact : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      PascalCenteredXiPrimeSideCofinalRadialContactAt ε W (Real.pi * r ε)) :
    PascalCenteredXiPrimeSideVanishingUpperEnvelopeAt W := by
  refine ⟨r, hr, ?_⟩
  have hpositive : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  filter_upwards [hcontact, hpositive] with ε hcontact hε
  exact
    (pascalCenteredXiPrimeSideCofinalRadialContactAt_iff_endpoint_le
      hε W).mp hcontact

/-! ## CS22-G/H: closure loop and named provider frontier -/

/-- This is the finite/cofinal half of the CS10--CS22 closure loop. Together
with `...cofinalRadialContactAt_iff_endpoint_le`, it displays

`finite arithmetic upper anchor ↔ cofinal radial contact ↔ endpoint upper bound`.
-/
theorem pascalCenteredXiPrimeSideCofinalUpperAnchor_radialContact_closure_loop
    {ε r : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    PascalCenteredXiPrimeSideCofinalFiniteUpperAnchorAt ε W r ↔
      PascalCenteredXiPrimeSideCofinalRadialContactAt ε W (Real.pi * r) :=
  pascalCenteredXiPrimeSideCofinalFiniteUpperAnchorAt_iff_cofinalRadialContactAt
    hε W

theorem pascalCenteredXiPrimeSideCofinalRadialContact_source_ledger
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    DεX ε W X =
        pascalCenteredXiMellinQuadraticArithmeticDefectApproximant ε W X ∧
      DεX ε W X =
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
  exact ⟨rfl, pascalCenteredXiPrimeSideGoodCutoff_source_ledger hε W X⟩

inductive PascalCenteredXiPrimeSideCofinalRadialContactGap : Prop
  | noIndependentCofinalRadialContactProvider

theorem pascalCenteredXiPrimeSideCofinalUpperAnchorGap_iff_radialContactGap :
    PascalCenteredXiPrimeSideCofinalFiniteUpperAnchorGap ↔
      PascalCenteredXiPrimeSideCofinalRadialContactGap := by
  constructor <;> intro _ <;> constructor

end DkMath.RH.CFBRCProjection
