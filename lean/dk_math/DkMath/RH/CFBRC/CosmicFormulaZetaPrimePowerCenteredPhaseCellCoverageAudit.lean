/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaNegativeFrequencyProfileDerivativeAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaPrimePowerCenteredPhaseCellCoverageAudit"

/-!
# CFZP-006Y: prime-power centered phase-cell coverage audit

This module changes the finite centered frequency interval to the
dimensionless angle `θ = u * T`.  The phase-cell hypotheses remain explicit
inputs: this file supplies exact coordinate and sign-transport lemmas, not a
prime-power distribution theorem or a universal event-sign theorem.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open DkMath.NumberTheory
open DkMath.NumberTheory.PrimitiveSet
open Filter
open MeasureTheory
open Set
open scoped ComplexConjugate Interval Topology

/-! ## A. Dimensionless phase derivative core -/

noncomputable def cfzpPhaseDerivativeSinCoeff (α θ : ℝ) : ℝ :=
  θ ^ 2 * (1 - α ^ 2) - 2 * (α * θ + 1)

noncomputable def cfzpPhaseDerivativeCore (α θ : ℝ) : ℝ :=
  cfzpPhaseDerivativeSinCoeff α θ * Real.sin θ +
    2 * θ * (α * θ + 1) * Real.cos θ

theorem cfzpNegativeFrequencyBoundaryProfileDerivativeCore_eq_phaseDerivativeCore
    {a T u : ℝ} (hT : T ≠ 0) :
    cfzpNegativeFrequencyBoundaryProfileDerivativeCore a T u =
      cfzpPhaseDerivativeCore (a / T) (u * T) := by
  unfold cfzpNegativeFrequencyBoundaryProfileDerivativeCore
    cfzpNegativeFrequencyBoundaryProfileDerivativeSinCoeff
    cfzpPhaseDerivativeCore cfzpPhaseDerivativeSinCoeff
  field_simp [hT]

/-! ## B. Rectangle phase aspect ratio -/

noncomputable def cfzpModePhaseAspectRatio
    (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  cfzpModePhaseAbscissa W / W.rectangle.T

theorem cfzpModePhaseAbscissa_pos
    (W : PascalCenteredXiResidueTransportWindow) :
    0 < cfzpModePhaseAbscissa W := by
  unfold cfzpModePhaseAbscissa
  linarith [W.rectangle.hσ]

theorem cfzpModePhaseAspectRatio_pos
    (W : PascalCenteredXiResidueTransportWindow) :
    0 < cfzpModePhaseAspectRatio W := by
  exact div_pos (cfzpModePhaseAbscissa_pos W) W.rectangle.hT

/-! ## C. Prime-power centered angular coordinates -/

noncomputable def cfzpPrimePowerPhaseAngleCenter
    (W : PascalCenteredXiResidueTransportWindow) (p j : ℕ) : ℝ :=
  W.rectangle.T * cfzpPrimePowerPhaseCenter p j

noncomputable def cfzpPrimePowerPhaseAngleHalfWidth
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  W.rectangle.T * ε

noncomputable def cfzpPrimePowerPhaseAngleLeft
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (p j : ℕ) : ℝ :=
  cfzpPrimePowerPhaseAngleCenter W p j -
    cfzpPrimePowerPhaseAngleHalfWidth ε W

noncomputable def cfzpPrimePowerPhaseAngleRight
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (p j : ℕ) : ℝ :=
  cfzpPrimePowerPhaseAngleCenter W p j +
    cfzpPrimePowerPhaseAngleHalfWidth ε W

theorem cfzpPrimePowerPhaseAngleCenter_eq_rectangleT_mul_phaseCenter
    (W : PascalCenteredXiResidueTransportWindow) (p j : ℕ) :
    cfzpPrimePowerPhaseAngleCenter W p j =
      W.rectangle.T * cfzpPrimePowerPhaseCenter p j := by
  rfl

theorem cfzpPrimePowerPhaseAngleLeft_eq_rectangleT_mul_phaseMagnitudeLeft
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (p j : ℕ) :
    cfzpPrimePowerPhaseAngleLeft ε W p j =
      W.rectangle.T * cfzpPrimePowerPhaseMagnitudeLeft ε p j := by
  unfold cfzpPrimePowerPhaseAngleLeft cfzpPrimePowerPhaseAngleCenter
    cfzpPrimePowerPhaseAngleHalfWidth cfzpPrimePowerPhaseMagnitudeLeft
  ring

theorem cfzpPrimePowerPhaseAngleRight_eq_rectangleT_mul_phaseMagnitudeRight
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (p j : ℕ) :
    cfzpPrimePowerPhaseAngleRight ε W p j =
      W.rectangle.T * cfzpPrimePowerPhaseMagnitudeRight ε p j := by
  unfold cfzpPrimePowerPhaseAngleRight cfzpPrimePowerPhaseAngleCenter
    cfzpPrimePowerPhaseAngleHalfWidth cfzpPrimePowerPhaseMagnitudeRight
  ring

theorem cfzpPrimePowerPhaseAngleHalfWidth_pos
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    0 < cfzpPrimePowerPhaseAngleHalfWidth ε W := by
  exact mul_pos W.rectangle.hT hε

theorem cfzpPrimePowerPhaseAngle_left_lt_right
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (p j : ℕ) :
    cfzpPrimePowerPhaseAngleLeft ε W p j <
      cfzpPrimePowerPhaseAngleRight ε W p j := by
  rw [cfzpPrimePowerPhaseAngleLeft_eq_rectangleT_mul_phaseMagnitudeLeft,
    cfzpPrimePowerPhaseAngleRight_eq_rectangleT_mul_phaseMagnitudeRight]
  exact mul_lt_mul_of_pos_left
    (cfzpPrimePowerPhaseMagnitude_left_lt_right hε p j) W.rectangle.hT

theorem cfzpPrimePowerPhaseAngles_pos_of_epsilon_lt_log_two
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) :
    0 < cfzpPrimePowerPhaseAngleLeft ε W p j ∧
      0 < cfzpPrimePowerPhaseAngleRight ε W p j := by
  have hmag := cfzpPrimePowerPhaseMagnitudes_pos_of_epsilon_lt_log_two
    hε hε2 hp hj
  rw [cfzpPrimePowerPhaseAngleLeft_eq_rectangleT_mul_phaseMagnitudeLeft,
    cfzpPrimePowerPhaseAngleRight_eq_rectangleT_mul_phaseMagnitudeRight]
  exact ⟨mul_pos W.rectangle.hT hmag.1, mul_pos W.rectangle.hT hmag.2⟩

theorem cfzpPrimePowerPhaseAngle_center_eq_T_mul_primePowerCenter
    (W : PascalCenteredXiResidueTransportWindow) (p j : ℕ) :
    cfzpPrimePowerPhaseAngleCenter W p j =
      W.rectangle.T * ((j : ℝ) * Real.log (p : ℝ)) := by
  unfold cfzpPrimePowerPhaseAngleCenter cfzpPrimePowerPhaseCenter
  rfl

/-! ## D. Phase cells and their algebraic sign consequences -/

def cfzpPhaseCellSinNonposCosNonpos (θ : ℝ) : Prop :=
  Real.sin θ ≤ 0 ∧ Real.cos θ ≤ 0

def cfzpPhaseCellSinNonposCosNonneg (θ : ℝ) : Prop :=
  Real.sin θ ≤ 0 ∧ 0 ≤ Real.cos θ

theorem cfzpPhaseDerivativeCore_nonpos_of_sinCoeff_nonneg_sin_nonpos_cos_nonpos
    {α θ : ℝ} (hα : 0 ≤ α) (hθ : 0 < θ)
    (hA : 0 ≤ cfzpPhaseDerivativeSinCoeff α θ)
    (hcell : cfzpPhaseCellSinNonposCosNonpos θ) :
    cfzpPhaseDerivativeCore α θ ≤ 0 := by
  have hA' :
      0 ≤ cfzpNegativeFrequencyBoundaryProfileDerivativeSinCoeff α 1 θ := by
    simpa [cfzpNegativeFrequencyBoundaryProfileDerivativeSinCoeff,
      cfzpPhaseDerivativeSinCoeff] using hA
  have h :=
    cfzpNegativeFrequencyBoundaryProfileDerivativeCore_nonpos_of_sinCoeff_nonneg_sin_nonpos_cos_nonpos
      (a := α) (T := 1) (u := θ) hα (by norm_num) hθ hA'
      (by simpa using hcell.1) (by simpa using hcell.2)
  simpa [cfzpNegativeFrequencyBoundaryProfileDerivativeCore,
    cfzpNegativeFrequencyBoundaryProfileDerivativeSinCoeff,
    cfzpPhaseDerivativeCore, cfzpPhaseDerivativeSinCoeff] using h

theorem cfzpPhaseDerivativeCore_nonneg_of_sinCoeff_nonpos_sin_nonpos_cos_nonneg
    {α θ : ℝ} (hα : 0 ≤ α) (hθ : 0 < θ)
    (hA : cfzpPhaseDerivativeSinCoeff α θ ≤ 0)
    (hcell : cfzpPhaseCellSinNonposCosNonneg θ) :
    0 ≤ cfzpPhaseDerivativeCore α θ := by
  have hA' :
      cfzpNegativeFrequencyBoundaryProfileDerivativeSinCoeff α 1 θ ≤ 0 := by
    simpa [cfzpNegativeFrequencyBoundaryProfileDerivativeSinCoeff,
      cfzpPhaseDerivativeSinCoeff] using hA
  have h :=
    cfzpNegativeFrequencyBoundaryProfileDerivativeCore_nonneg_of_sinCoeff_nonpos_sin_nonpos_cos_nonneg
      (a := α) (T := 1) (u := θ) hα (by norm_num) hθ hA'
      (by simpa using hcell.1) (by simpa using hcell.2)
  simpa [cfzpNegativeFrequencyBoundaryProfileDerivativeCore,
    cfzpNegativeFrequencyBoundaryProfileDerivativeSinCoeff,
    cfzpPhaseDerivativeCore, cfzpPhaseDerivativeSinCoeff] using h

/-! ## E. Angular coverage transports to frequency coverage -/

theorem cfzpPrimePowerDerivativeCore_nonpos_on_centeredInterval_of_phaseCore_nonpos
    {a T l r : ℝ} (_ha : 0 ≤ a) (hT : 0 < T) (hl : 0 < l) (_hlr : l < r)
    (hphase : ∀ θ ∈ Set.Ioo (l * T) (r * T),
      cfzpPhaseDerivativeCore (a / T) θ ≤ 0) :
    ∀ u ∈ Set.Ioo l r,
      cfzpNegativeFrequencyBoundaryProfileDerivativeCore a T u ≤ 0 := by
  intro u hu
  have huPos : 0 < u := lt_trans hl hu.1
  have hθ : u * T ∈ Set.Ioo (l * T) (r * T) := by
    constructor <;> nlinarith [hT, hu.1, hu.2]
  rw [cfzpNegativeFrequencyBoundaryProfileDerivativeCore_eq_phaseDerivativeCore
    (a := a) (T := T) (u := u) hT.ne']
  exact hphase (u * T) hθ

theorem cfzpPrimePowerDerivativeCore_nonneg_on_centeredInterval_of_phaseCore_nonneg
    {a T l r : ℝ} (_ha : 0 ≤ a) (hT : 0 < T) (hl : 0 < l) (_hlr : l < r)
    (hphase : ∀ θ ∈ Set.Ioo (l * T) (r * T),
      0 ≤ cfzpPhaseDerivativeCore (a / T) θ) :
    ∀ u ∈ Set.Ioo l r,
      0 ≤ cfzpNegativeFrequencyBoundaryProfileDerivativeCore a T u := by
  intro u hu
  have huPos : 0 < u := lt_trans hl hu.1
  have hθ : u * T ∈ Set.Ioo (l * T) (r * T) := by
    constructor <;> nlinarith [hT, hu.1, hu.2]
  rw [cfzpNegativeFrequencyBoundaryProfileDerivativeCore_eq_phaseDerivativeCore
    (a := a) (T := T) (u := u) hT.ne']
  exact hphase (u * T) hθ

theorem cfzpPrimePowerCenteredAngle_Icc_subset_of_cell_bounds
    {θL θR cL cR : ℝ} (hleft : cL ≤ θL) (hright : θR ≤ cR) :
    Set.Icc θL θR ⊆ Set.Icc cL cR := by
  intro θ hθ
  exact ⟨hleft.trans hθ.1, hθ.2.trans hright⟩

/-! ## F. Phase-core coverage gives one-event sign -/

theorem cfzpPrimePowerBranchFreeTrigEvent_nonneg_of_phaseDerivativeCore_nonpos_on_centeredAngle
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j)
    (hphase : ∀ θ ∈ Set.Ioo
        (cfzpPrimePowerPhaseAngleLeft ε W p j)
        (cfzpPrimePowerPhaseAngleRight ε W p j),
      cfzpPhaseDerivativeCore (cfzpModePhaseAspectRatio W) θ ≤ 0) :
    0 ≤ cfzpPrimePowerBranchFreeTrigEvent ε W p j := by
  have hmag := cfzpPrimePowerPhaseMagnitudes_pos_of_epsilon_lt_log_two
    hε hε2 hp hj
  have hT := W.rectangle.hT
  have hcore : ∀ u ∈ Set.Ioo
      (cfzpPrimePowerPhaseMagnitudeLeft ε p j)
      (cfzpPrimePowerPhaseMagnitudeRight ε p j),
      cfzpNegativeFrequencyBoundaryProfileDerivativeCore
        (cfzpModePhaseAbscissa W) W.rectangle.T u ≤ 0 := by
    intro u hu
    have hθ : u * W.rectangle.T ∈ Set.Ioo
        (cfzpPrimePowerPhaseAngleLeft ε W p j)
        (cfzpPrimePowerPhaseAngleRight ε W p j) := by
      rw [cfzpPrimePowerPhaseAngleLeft_eq_rectangleT_mul_phaseMagnitudeLeft,
        cfzpPrimePowerPhaseAngleRight_eq_rectangleT_mul_phaseMagnitudeRight]
      constructor <;> nlinarith [hT, hu.1, hu.2]
    have hphase' := hphase (u * W.rectangle.T) hθ
    rw [cfzpNegativeFrequencyBoundaryProfileDerivativeCore_eq_phaseDerivativeCore
      (a := cfzpModePhaseAbscissa W) (T := W.rectangle.T) (u := u) hT.ne']
    simpa [cfzpModePhaseAspectRatio] using hphase'
  exact cfzpPrimePowerBranchFreeTrigEvent_nonneg_of_derivativeCore_nonpos_on_centeredInterval
    hε hε2 W hp hj hcore

theorem cfzpPrimePowerBranchFreeTrigEvent_nonpos_of_phaseDerivativeCore_nonneg_on_centeredAngle
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j)
    (hphase : ∀ θ ∈ Set.Ioo
        (cfzpPrimePowerPhaseAngleLeft ε W p j)
        (cfzpPrimePowerPhaseAngleRight ε W p j),
      0 ≤ cfzpPhaseDerivativeCore (cfzpModePhaseAspectRatio W) θ) :
    cfzpPrimePowerBranchFreeTrigEvent ε W p j ≤ 0 := by
  have hmag := cfzpPrimePowerPhaseMagnitudes_pos_of_epsilon_lt_log_two
    hε hε2 hp hj
  have hT := W.rectangle.hT
  have hcore : ∀ u ∈ Set.Ioo
      (cfzpPrimePowerPhaseMagnitudeLeft ε p j)
      (cfzpPrimePowerPhaseMagnitudeRight ε p j),
      0 ≤ cfzpNegativeFrequencyBoundaryProfileDerivativeCore
        (cfzpModePhaseAbscissa W) W.rectangle.T u := by
    intro u hu
    have hθ : u * W.rectangle.T ∈ Set.Ioo
        (cfzpPrimePowerPhaseAngleLeft ε W p j)
        (cfzpPrimePowerPhaseAngleRight ε W p j) := by
      rw [cfzpPrimePowerPhaseAngleLeft_eq_rectangleT_mul_phaseMagnitudeLeft,
        cfzpPrimePowerPhaseAngleRight_eq_rectangleT_mul_phaseMagnitudeRight]
      constructor <;> nlinarith [hT, hu.1, hu.2]
    have hphase' := hphase (u * W.rectangle.T) hθ
    rw [cfzpNegativeFrequencyBoundaryProfileDerivativeCore_eq_phaseDerivativeCore
      (a := cfzpModePhaseAbscissa W) (T := W.rectangle.T) (u := u) hT.ne']
    simpa [cfzpModePhaseAspectRatio] using hphase'
  exact cfzpPrimePowerBranchFreeTrigEvent_nonpos_of_derivativeCore_nonneg_on_centeredInterval
    hε hε2 W hp hj hcore

/-! ## G. Explicit phase-cell coverage adapters -/

theorem cfzpPrimePowerBranchFreeTrigEvent_nonneg_of_nonposPhaseCellCoverage
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j)
    (hA : ∀ θ ∈ Set.Ioo
        (cfzpPrimePowerPhaseAngleLeft ε W p j)
        (cfzpPrimePowerPhaseAngleRight ε W p j),
      0 ≤ cfzpPhaseDerivativeSinCoeff (cfzpModePhaseAspectRatio W) θ)
    (hcoverage : ∀ θ ∈ Set.Ioo
        (cfzpPrimePowerPhaseAngleLeft ε W p j)
        (cfzpPrimePowerPhaseAngleRight ε W p j),
      cfzpPhaseCellSinNonposCosNonpos θ) :
    0 ≤ cfzpPrimePowerBranchFreeTrigEvent ε W p j := by
  apply cfzpPrimePowerBranchFreeTrigEvent_nonneg_of_phaseDerivativeCore_nonpos_on_centeredAngle
    hε hε2 W hp hj
  intro θ hθ
  exact cfzpPhaseDerivativeCore_nonpos_of_sinCoeff_nonneg_sin_nonpos_cos_nonpos
    (by exact div_nonneg (cfzpModePhaseAbscissa_pos W).le W.rectangle.hT.le)
    (by exact lt_trans (cfzpPrimePowerPhaseAngles_pos_of_epsilon_lt_log_two
      hε hε2 W hp hj).1 hθ.1)
    (hA θ hθ) (hcoverage θ hθ)

theorem cfzpPrimePowerBranchFreeTrigEvent_nonpos_of_nonnegPhaseCellCoverage
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j)
    (hA : ∀ θ ∈ Set.Ioo
        (cfzpPrimePowerPhaseAngleLeft ε W p j)
        (cfzpPrimePowerPhaseAngleRight ε W p j),
      cfzpPhaseDerivativeSinCoeff (cfzpModePhaseAspectRatio W) θ ≤ 0)
    (hcoverage : ∀ θ ∈ Set.Ioo
        (cfzpPrimePowerPhaseAngleLeft ε W p j)
        (cfzpPrimePowerPhaseAngleRight ε W p j),
      cfzpPhaseCellSinNonposCosNonneg θ) :
    cfzpPrimePowerBranchFreeTrigEvent ε W p j ≤ 0 := by
  apply cfzpPrimePowerBranchFreeTrigEvent_nonpos_of_phaseDerivativeCore_nonneg_on_centeredAngle
    hε hε2 W hp hj
  intro θ hθ
  exact cfzpPhaseDerivativeCore_nonneg_of_sinCoeff_nonpos_sin_nonpos_cos_nonneg
    (by exact div_nonneg (cfzpModePhaseAbscissa_pos W).le W.rectangle.hT.le)
    (by exact lt_trans (cfzpPrimePowerPhaseAngles_pos_of_epsilon_lt_log_two
      hε hε2 W hp hj).1 hθ.1)
    (hA θ hθ) (hcoverage θ hθ)

/-! ## H. Deliberate frontier -/

inductive CfzpPrimePowerPhaseCellArithmeticCoverageGap : Prop
  | noIndependentPrimePowerArithmeticCenterPhaseCellCoverageProvider

end DkMath.RH.CFBRCProjection
