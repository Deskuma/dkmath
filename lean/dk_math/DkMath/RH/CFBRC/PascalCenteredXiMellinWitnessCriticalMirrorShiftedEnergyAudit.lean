/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiMellinWitnessCriticalMirrorWholeSourceAudit
import DkMath.RH.CFBRC.PascalCenteredXiMellinWitnessShiftedEnergyDominanceAudit
import Mathlib.Tactic

/-!
# GWSS-003H6: shifted-energy mirror parity and paired dominance collapse

This module transports the integrated shifted-energy readouts of GWSS-003G
through the finite canonical mirror transport of GWSS-003H5.  The `1`
reference difference is mirror-odd, while the `I` reference difference is
mirror-even.  Consequently, same-orientation paired dominance collapses the
`1` channel to equality, whereas it is redundant in the `I` channel.

All statements are finite-window statements.  They do not provide a new
positivity or dominance hypothesis, and they do not assert a limit, GWSS-004,
Guinand--Weil, or RH.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open MeasureTheory
open scoped BigOperators Interval Topology

/-! ## H8-A/B: shifted-difference mirror parity -/

/-- The integrated `1`-reference shifted-energy difference is odd under the
canonical critical mirror. -/
theorem pascalCenteredXiMellinCanonicalShiftedEnergyDifference_one_mirror
    {R ε : ℝ}
    (hε : 0 < ε)
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ)
    (hτ : ∀ i, τ i ≠ 0)
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R))
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinWitnessWholeShiftedPlusEnergy ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
          (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W X -
      pascalCenteredXiMellinWitnessWholeShiftedMinusEnergy ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
          (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W X =
      -(pascalCenteredXiMellinWitnessWholeShiftedPlusEnergy ε τ
          (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
          W X -
        pascalCenteredXiMellinWitnessWholeShiftedMinusEnergy ε τ
          (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
          W X) := by
  have hmirror := pascalCenteredXiMellinCanonicalWholeSource_channels_mirror
    hε τ hdet j W X
  calc
    _ = 4 * (pascalCenteredXiMellinGeneralTauWitnessWholeSource ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
          (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W X).re :=
      pascalCenteredXiMellinWitnessWholeShiftedEnergyDifference_one_eq_four_mul_wholeSource_re
        hε τ _ hτ W X
    _ = 4 * (-(pascalCenteredXiMellinGeneralTauWitnessWholeSource ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
        W X).re) := by rw [hmirror.1]
    _ = -(4 * (pascalCenteredXiMellinGeneralTauWitnessWholeSource ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
        W X).re) := by ring
    _ = _ := by
      rw [pascalCenteredXiMellinWitnessWholeShiftedEnergyDifference_one_eq_four_mul_wholeSource_re
        hε τ _ hτ W X]

/-- The integrated `I`-reference shifted-energy difference is even under the
canonical critical mirror. -/
theorem pascalCenteredXiMellinCanonicalShiftedEnergyDifference_I_mirror
    {R ε : ℝ}
    (hε : 0 < ε)
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ)
    (hτ : ∀ i, τ i ≠ 0)
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R))
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinWitnessWholeShiftedIPlusEnergy ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
          (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W X -
      pascalCenteredXiMellinWitnessWholeShiftedIMinusEnergy ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
          (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W X =
      pascalCenteredXiMellinWitnessWholeShiftedIPlusEnergy ε τ
          (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
          W X -
        pascalCenteredXiMellinWitnessWholeShiftedIMinusEnergy ε τ
          (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
          W X := by
  have hmirror := pascalCenteredXiMellinCanonicalWholeSource_channels_mirror
    hε τ hdet j W X
  calc
    _ = 4 * (pascalCenteredXiMellinGeneralTauWitnessWholeSource ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
          (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W X).im :=
      pascalCenteredXiMellinWitnessWholeShiftedEnergyDifference_I_eq_four_mul_wholeSource_im
        hε τ _ hτ W X
    _ = 4 * (pascalCenteredXiMellinGeneralTauWitnessWholeSource ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
        W X).im := by rw [hmirror.2]
    _ = _ := by
      rw [pascalCenteredXiMellinWitnessWholeShiftedEnergyDifference_I_eq_four_mul_wholeSource_im
        hε τ _ hτ W X]

/-! ## H8-C: `1`-reference dominance reversal -/

/-- Same-orientation `1`-reference dominance at the mirror endpoint is
exactly the opposite order at the original endpoint.  This transports an
order proposition; it does not establish either order. -/
theorem pascalCenteredXiMellinCanonicalShiftedEnergy_one_dominance_mirror_iff
    {R ε : ℝ}
    (hε : 0 < ε)
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ)
    (hτ : ∀ i, τ i ≠ 0)
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R))
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    (pascalCenteredXiMellinWitnessWholeShiftedMinusEnergy ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
          (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W X ≤
      pascalCenteredXiMellinWitnessWholeShiftedPlusEnergy ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
          (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W X) ↔
    pascalCenteredXiMellinWitnessWholeShiftedPlusEnergy ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
        W X ≤
      pascalCenteredXiMellinWitnessWholeShiftedMinusEnergy ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
        W X := by
  have hΔ := pascalCenteredXiMellinCanonicalShiftedEnergyDifference_one_mirror
    hε τ hτ hdet j W X
  constructor <;> intro h
  · linarith
  · linarith

/-! ## H8-D: paired `1`-dominance collapse -/

/-- Same-orientation `1`-dominance at both mirror endpoints is equivalent to
equality of the two original `1`-reference energies. -/
theorem pascalCenteredXiMellinCanonicalShiftedEnergy_one_paired_dominance_iff_energy_eq
    {R ε : ℝ}
    (hε : 0 < ε)
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ)
    (hτ : ∀ i, τ i ≠ 0)
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R))
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    ((pascalCenteredXiMellinWitnessWholeShiftedMinusEnergy ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
        W X ≤
      pascalCenteredXiMellinWitnessWholeShiftedPlusEnergy ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
        W X) ∧
    (pascalCenteredXiMellinWitnessWholeShiftedMinusEnergy ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
          (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W X ≤
      pascalCenteredXiMellinWitnessWholeShiftedPlusEnergy ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
          (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W X)) ↔
    pascalCenteredXiMellinWitnessWholeShiftedPlusEnergy ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
        W X =
      pascalCenteredXiMellinWitnessWholeShiftedMinusEnergy ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
        W X := by
  have hrev := pascalCenteredXiMellinCanonicalShiftedEnergy_one_dominance_mirror_iff
    hε τ hτ hdet j W X
  constructor
  · intro h
    linarith [h.1, hrev.mp h.2]
  · intro h
    constructor
    · linarith
    · apply hrev.mpr
      linarith

/-- The same paired `1`-dominance condition is equivalent to vanishing of the
real whole-source channel.  This is a conditional collapse, not a positivity
provider. -/
theorem pascalCenteredXiMellinCanonicalShiftedEnergy_one_paired_dominance_iff_wholeSource_re_eq_zero
    {R ε : ℝ}
    (hε : 0 < ε)
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ)
    (hτ : ∀ i, τ i ≠ 0)
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R))
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    ((pascalCenteredXiMellinWitnessWholeShiftedMinusEnergy ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
        W X ≤
      pascalCenteredXiMellinWitnessWholeShiftedPlusEnergy ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
        W X) ∧
    (pascalCenteredXiMellinWitnessWholeShiftedMinusEnergy ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
          (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W X ≤
      pascalCenteredXiMellinWitnessWholeShiftedPlusEnergy ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
          (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W X)) ↔
    (pascalCenteredXiMellinGeneralTauWitnessWholeSource ε τ
      (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
      W X).re = 0 := by
  have horder := pascalCenteredXiMellinWitnessWholeShiftedEnergy_order_iff_wholeSource_re_nonneg
    hε τ (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
    hτ W X
  have horderMirror := pascalCenteredXiMellinWitnessWholeShiftedEnergy_order_iff_wholeSource_re_nonneg
    hε τ (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
      (pascalCenteredXiSquaredOrbitMirrorIndex R j)) hτ W X
  have hmirror := pascalCenteredXiMellinCanonicalWholeSource_channels_mirror
    hε τ hdet j W X
  constructor
  · intro h
    have hj : 0 ≤ (pascalCenteredXiMellinGeneralTauWitnessWholeSource ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
        W X).re := horder.mp h.1
    have hm : 0 ≤ (pascalCenteredXiMellinGeneralTauWitnessWholeSource ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
          (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W X).re :=
      horderMirror.mp h.2
    rw [hmirror.1] at hm
    linarith
  · intro hzero
    constructor
    · apply horder.mpr
      rw [hzero]
    · apply horderMirror.mpr
      rw [hmirror.1, hzero]
      norm_num

/-! ## H8-E: `I`-reference dominance invariance -/

/-- `I`-reference dominance is invariant under the canonical mirror. -/
theorem pascalCenteredXiMellinCanonicalShiftedEnergy_I_dominance_mirror_iff
    {R ε : ℝ}
    (hε : 0 < ε)
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ)
    (hτ : ∀ i, τ i ≠ 0)
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R))
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    (pascalCenteredXiMellinWitnessWholeShiftedIMinusEnergy ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
          (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W X ≤
      pascalCenteredXiMellinWitnessWholeShiftedIPlusEnergy ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
          (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W X) ↔
    pascalCenteredXiMellinWitnessWholeShiftedIMinusEnergy ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
        W X ≤
      pascalCenteredXiMellinWitnessWholeShiftedIPlusEnergy ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
        W X := by
  have horder := pascalCenteredXiMellinWitnessWholeShiftedIEnergy_order_iff_wholeSource_im_nonneg
    hε τ (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
    hτ W X
  have horderMirror := pascalCenteredXiMellinWitnessWholeShiftedIEnergy_order_iff_wholeSource_im_nonneg
    hε τ (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
      (pascalCenteredXiSquaredOrbitMirrorIndex R j)) hτ W X
  have hmirror := pascalCenteredXiMellinCanonicalWholeSource_channels_mirror
    hε τ hdet j W X
  constructor
  · intro h
    apply horder.mpr
    rw [← hmirror.2]
    exact horderMirror.mp h
  · intro h
    apply horderMirror.mpr
    rw [hmirror.2]
    exact horder.mp h

/-- Paired same-orientation `I` dominance is redundant: it is equivalent to
the original endpoint's dominance and supplies no opposite inequality. -/
theorem pascalCenteredXiMellinCanonicalShiftedEnergy_I_paired_dominance_iff
    {R ε : ℝ}
    (hε : 0 < ε)
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ)
    (hτ : ∀ i, τ i ≠ 0)
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R))
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    ((pascalCenteredXiMellinWitnessWholeShiftedIMinusEnergy ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
        W X ≤
      pascalCenteredXiMellinWitnessWholeShiftedIPlusEnergy ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
        W X) ∧
    (pascalCenteredXiMellinWitnessWholeShiftedIMinusEnergy ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
          (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W X ≤
      pascalCenteredXiMellinWitnessWholeShiftedIPlusEnergy ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
          (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W X)) ↔
    pascalCenteredXiMellinWitnessWholeShiftedIMinusEnergy ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
        W X ≤
      pascalCenteredXiMellinWitnessWholeShiftedIPlusEnergy ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
        W X := by
  have hmirror := pascalCenteredXiMellinCanonicalShiftedEnergy_I_dominance_mirror_iff
    hε τ hτ hdet j W X
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, hmirror.mpr h⟩

/-! ## H8-F: compact channel certificate -/

/-- Compactly packages the asymmetric mirror parity of the two integrated
shifted-energy channels. -/
theorem pascalCenteredXiMellinCanonicalShiftedEnergy_mirror_parity
    {R ε : ℝ}
    (hε : 0 < ε)
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ)
    (hτ : ∀ i, τ i ≠ 0)
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R))
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    (pascalCenteredXiMellinWitnessWholeShiftedPlusEnergy ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
          (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W X -
      pascalCenteredXiMellinWitnessWholeShiftedMinusEnergy ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
          (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W X =
      -(pascalCenteredXiMellinWitnessWholeShiftedPlusEnergy ε τ
          (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
          W X -
        pascalCenteredXiMellinWitnessWholeShiftedMinusEnergy ε τ
          (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
          W X)) ∧
    (pascalCenteredXiMellinWitnessWholeShiftedIPlusEnergy ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
          (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W X -
      pascalCenteredXiMellinWitnessWholeShiftedIMinusEnergy ε τ
        (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ
          (pascalCenteredXiSquaredOrbitMirrorIndex R j)) W X =
      pascalCenteredXiMellinWitnessWholeShiftedIPlusEnergy ε τ
          (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
          W X -
        pascalCenteredXiMellinWitnessWholeShiftedIMinusEnergy ε τ
          (pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j)
          W X) := by
  exact ⟨pascalCenteredXiMellinCanonicalShiftedEnergyDifference_one_mirror
      hε τ hτ hdet j W X,
    pascalCenteredXiMellinCanonicalShiftedEnergyDifference_I_mirror
      hε τ hτ hdet j W X⟩

end DkMath.RH.CFBRCProjection
