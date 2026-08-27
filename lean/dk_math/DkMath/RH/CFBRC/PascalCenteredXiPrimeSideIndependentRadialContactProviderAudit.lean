/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideCofinalRadialContactAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideSignAudit
import Mathlib.Tactic

/-!
# CS23: independent radial-contact provider audit

CS22 closed the adapter loop but did not produce a source estimate.  This
module therefore exposes the complete finite normalized source as an exact
four-term decomposition and records the remaining signed-mass/remainder
frontier.

The exact decomposition is a Green-B result: it is a source-complete identity,
not an independent upper-contact estimate.  In particular, no endpoint sign,
zero-side theorem, infinite exchange, or RH conclusion is used here.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

local notation "DεX" => pascalCenteredXiMellinQuadraticArithmeticDefectApproximant
local notation "GεX" => pascalCenteredXiPrimeSideFiniteRadialContactDeficit

/-! ## CS23-A: complete finite source expansion -/

/-- The complete normalized finite source, with prime, archimedean,
elementary, and top-horizontal components all retained. -/
noncomputable def pascalCenteredXiPrimeSideIndependentCompleteSourceReal
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℝ :=
  pascalCenteredXiMellinQuadraticNormalizedPrimeContribution ε W X +
  pascalCenteredXiMellinQuadraticNormalizedArchimedeanContribution ε W +
  pascalCenteredXiMellinQuadraticNormalizedElementaryContribution ε W +
  pascalCenteredXiMellinQuadraticNormalizedTopContribution ε W

theorem pascalCenteredXiPrimeSideIndependentCompleteSourceReal_eq_normalized_re
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideIndependentCompleteSourceReal ε W X =
      (pascalCenteredXiMellinQuadraticNormalizedArithmeticApproximant ε W X).re := by
  simpa [pascalCenteredXiPrimeSideIndependentCompleteSourceReal] using
    (pascalCenteredXiMellinQuadraticNormalizedArithmeticApproximant_re_eq_four_terms
      hε W X).symm

/-! ## CS23-B: source-complete radial deficit identity -/

theorem pascalCenteredXiPrimeSideIndependentCompleteSource_radialDeficit_eq
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    GεX ε W X =
      Real.pi *
        (pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
          pascalCenteredXiPrimeSideIndependentCompleteSourceReal ε W X) := by
  have hG := pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_pi_mul_defect
    hε W X
  have hsource := pascalCenteredXiPrimeSideIndependentCompleteSourceReal_eq_normalized_re
    hε W X
  rw [hG]
  unfold pascalCenteredXiMellinQuadraticArithmeticDefectApproximant
  rw [hsource]

theorem pascalCenteredXiPrimeSideIndependentCompleteSource_contact_iff
    {ε r : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    DεX ε W X ≤ r ↔
      Real.pi *
          (pascalCenteredXiFixedRadialSecondMomentFunctional W.R - r) ≤
        Real.pi * pascalCenteredXiPrimeSideIndependentCompleteSourceReal ε W X := by
  have hsource := pascalCenteredXiPrimeSideIndependentCompleteSourceReal_eq_normalized_re
    hε W X
  have hsurface :=
    pascalCenteredXiPrimeSideQuadraticization_scalarSurface_eq_pi_mul_normalizedArithmetic_re
      hε W X
  rw [pascalCenteredXiPrimeSideFiniteRadialContactDeficit_le_iff_scalarSurface_ge hε W X]
  rw [hsurface, ← hsource]

/-! ## CS23-C: signed-mass/remainder logic -/

/-- A nonnegative mass can only lower a signed-mass decomposition below its
remainder.  This is the exact order step needed by a future source estimate. -/
theorem pascalCenteredXiPrimeSideSignedMass_sub_le_remainder
    {G M R : ℝ} (hdecomp : G = R - M) (hM : 0 ≤ M) :
    G ≤ R := by
  linarith

/-- If an independently supplied source decomposition has a small remainder,
then it gives the corresponding finite radial contact.  This is an adapter
for a future source theorem; it does not construct the decomposition. -/
theorem pascalCenteredXiPrimeSideIndependentSignedMassRemainder_finite_contact
    {ε η M R : ℝ} (_hε : 0 < ε) (_hη : 0 < η)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (hdecomp : GεX ε W X = R - M)
    (hM : 0 ≤ M) (hR : R ≤ η) :
    GεX ε W X ≤ η := by
  exact (pascalCenteredXiPrimeSideSignedMass_sub_le_remainder hdecomp hM).trans hR

/-- The signed-mass equation and mass nonnegativity alone do not imply the
desired nonpositivity.  A small-remainder estimate is logically essential. -/
theorem pascalCenteredXiPrimeSideSignedMass_nonneg_alone_not_nonpos :
    ¬ (∀ G M R : ℝ, G = R - M → 0 ≤ M → G ≤ 0) := by
  intro h
  have hcounter := h (1 : ℝ) 0 1 (by norm_num) (by norm_num)
  norm_num at hcounter

/-! ## CS23-D: conditional cofinal adapter -/

/-- A genuine source theorem of the signed-mass/remainder shape would imply
zero-target cofinal radial contact.  The hypothesis is deliberately stated
as a source certificate and is not provided by this module. -/
theorem pascalCenteredXiPrimeSideIndependentSignedMassRemainder_implies_cofinalRadialContactZero
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (hsource : ∀ η : ℝ, 0 < η → ∀ N : ℕ, ∃ X : ℕ, ∃ M R : ℝ,
      N ≤ X ∧ GεX ε W X = R - M ∧ 0 ≤ M ∧ R ≤ η) :
    PascalCenteredXiPrimeSideCofinalRadialContactZeroAt ε W := by
  intro η hη N
  rcases hsource η hη N with ⟨X, M, R, hNX, hdecomp, hM, hR⟩
  refine ⟨X, hNX, ?_⟩
  simpa using
    (pascalCenteredXiPrimeSideIndependentSignedMassRemainder_finite_contact
      hε hη W X hdecomp hM hR)

/-! ## CS23-E: provider frontier -/

inductive PascalCenteredXiPrimeSideIndependentRadialContactProviderGap : Prop
  | noIndependentSourceSignedMassRemainderCertificate

end DkMath.RH.CFBRCProjection
