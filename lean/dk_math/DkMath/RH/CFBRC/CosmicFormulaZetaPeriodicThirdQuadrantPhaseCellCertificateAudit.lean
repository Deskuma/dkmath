/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaQuantitativePhaseCoreMarginSynthesisAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaPeriodicThirdQuadrantPhaseCellCertificateAudit"

/-!
# CFZP-026: periodic third-quadrant phase-cell certificates

This module turns a finite strict third-quadrant phase-cell hit into an
explicit phase-core margin.  The construction is periodic in the cell index,
uses endpoint coefficient floors, and feeds the resulting margin into the
CFZP-025/024 interfaces.  Cofinal phase hits and any distribution theorem for
prime-power phases remain explicit frontier data.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.NumberTheory
open Set

/-! ## Gate A: periodic third-quadrant cells -/

/-- The left endpoint of the `k`-th strict third-quadrant cell. -/
noncomputable def cfzp026ThirdQuadrantCellLeft (k : ℕ) (τ : ℝ) : ℝ :=
  Real.pi + 2 * Real.pi * (k : ℝ) + τ

/-- The right endpoint of the `k`-th strict third-quadrant cell. -/
noncomputable def cfzp026ThirdQuadrantCellRight (k : ℕ) (τ : ℝ) : ℝ :=
  3 * Real.pi / 2 + 2 * Real.pi * (k : ℝ) - τ

/-- The cell is nonempty when its interior trim is at most `π/4`. -/
theorem cfzp026ThirdQuadrantCellLeft_le_right
    {k : ℕ} {τ : ℝ} (hτ : τ ≤ Real.pi / 4) :
    cfzp026ThirdQuadrantCellLeft k τ ≤
      cfzp026ThirdQuadrantCellRight k τ := by
  unfold cfzp026ThirdQuadrantCellLeft cfzp026ThirdQuadrantCellRight
  nlinarith

/-- Every trimmed third-quadrant cell starts at a positive angle. -/
theorem cfzp026ThirdQuadrantCellLeft_pos
    {k : ℕ} {τ : ℝ} (hτ : 0 ≤ τ) :
    0 < cfzp026ThirdQuadrantCellLeft k τ := by
  unfold cfzp026ThirdQuadrantCellLeft
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  nlinarith [Real.pi_pos]

/-! ## Gate B: periodic trigonometric margins -/

/-- A point in a trimmed periodic third-quadrant cell has both trigonometric
coordinates bounded above by the same negative boundary value. -/
theorem cfzp026_sin_cos_le_neg_sin_of_mem_thirdQuadrantCell
    {k : ℕ} {τ θ : ℝ} (hτ : 0 ≤ τ) (hτ4 : τ ≤ Real.pi / 4)
    (hθ : θ ∈ Set.Icc
      (cfzp026ThirdQuadrantCellLeft k τ)
      (cfzp026ThirdQuadrantCellRight k τ)) :
    Real.sin θ ≤ -Real.sin τ ∧ Real.cos θ ≤ -Real.sin τ := by
  have hθL : Real.pi + 2 * Real.pi * (k : ℝ) + τ ≤ θ := by
    exact hθ.1
  have hθR : θ ≤ 3 * Real.pi / 2 + 2 * Real.pi * (k : ℝ) - τ := by
    exact hθ.2
  let x : ℝ := θ - (k : ℝ) * (2 * Real.pi)
  let y : ℝ := x - Real.pi
  have hxL : Real.pi + τ ≤ x := by
    dsimp [x]
    nlinarith [hθL]
  have hxR : x ≤ 3 * Real.pi / 2 - τ := by
    dsimp [x]
    nlinarith [hθR]
  have hy0 : 0 ≤ y := by
    dsimp [y]
    nlinarith [hxL, hτ]
  have hytau : τ ≤ y := by
    dsimp [y]
    nlinarith [hxL]
  have hyR : y ≤ Real.pi / 2 - τ := by
    dsimp [y]
    nlinarith [hxR]
  have hsinY : Real.sin τ ≤ Real.sin y := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · nlinarith [Real.pi_pos, hτ]
    · nlinarith [hyR, hτ]
    · exact hytau
  have hcosY : Real.sin τ ≤ Real.cos y := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi hy0
      (by nlinarith [Real.pi_pos, hτ]) hyR
    simpa only [Real.cos_pi_div_two_sub] using h
  have hsinX : Real.sin x = -Real.sin y := by
    have hxy : x = y + Real.pi := by
      dsimp [y]
      ring
    rw [hxy, Real.sin_add_pi]
  have hcosX : Real.cos x = -Real.cos y := by
    have hxy : x = y + Real.pi := by
      dsimp [y]
      ring
    rw [hxy, Real.cos_add_pi]
  have hsinPeriod : Real.sin θ = Real.sin x := by
    have hθx : θ = x + (k : ℝ) * (2 * Real.pi) := by
      dsimp [x]
      ring
    rw [hθx, Real.sin_add_nat_mul_two_pi]
  have hcosPeriod : Real.cos θ = Real.cos x := by
    have hθx : θ = x + (k : ℝ) * (2 * Real.pi) := by
      dsimp [x]
      ring
    rw [hθx, Real.cos_add_nat_mul_two_pi]
  constructor
  · calc
      Real.sin θ = Real.sin x := hsinPeriod
      _ = -Real.sin y := hsinX
      _ ≤ -Real.sin τ := neg_le_neg hsinY
  · calc
      Real.cos θ = Real.cos x := hcosPeriod
      _ = -Real.cos y := hcosX
      _ ≤ -Real.sin τ := neg_le_neg hcosY

/-! ## Gate C/D: centered interval containment and arithmetic form -/

/-- A prime-power centered angle interval is contained in a periodic cell. -/
def Cfzp026PrimePowerCenteredAngleContainedInThirdQuadrantCell
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j k : ℕ) (τ : ℝ) : Prop :=
  cfzp026ThirdQuadrantCellLeft k τ ≤
      cfzpPrimePowerPhaseAngleLeft ε W p j ∧
    cfzpPrimePowerPhaseAngleRight ε W p j ≤
      cfzp026ThirdQuadrantCellRight k τ

/-- The containment property expressed using the center and half-width. -/
theorem cfzp026PrimePowerCenteredAngleContained_iff_center_halfWidth
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j k : ℕ) (τ : ℝ) :
    Cfzp026PrimePowerCenteredAngleContainedInThirdQuadrantCell ε W p j k τ ↔
      cfzp026ThirdQuadrantCellLeft k τ +
          cfzpPrimePowerPhaseAngleHalfWidth ε W ≤
        cfzpPrimePowerPhaseAngleCenter W p j ∧
      cfzpPrimePowerPhaseAngleCenter W p j +
          cfzpPrimePowerPhaseAngleHalfWidth ε W ≤
        cfzp026ThirdQuadrantCellRight k τ := by
  unfold Cfzp026PrimePowerCenteredAngleContainedInThirdQuadrantCell
    cfzpPrimePowerPhaseAngleLeft cfzpPrimePowerPhaseAngleRight
  constructor <;> intro h <;> constructor <;> nlinarith [h.1, h.2]

/-- The finite arithmetic target for a prime-power phase hit. -/
def Cfzp026PrimePowerQuantitativeThirdQuadrantHit
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j k : ℕ) (τ : ℝ) : Prop :=
  cfzp026ThirdQuadrantCellLeft k τ + W.rectangle.T * ε ≤
      W.rectangle.T * ((j : ℝ) * Real.log (p : ℝ)) ∧
    W.rectangle.T * ((j : ℝ) * Real.log (p : ℝ)) + W.rectangle.T * ε ≤
      cfzp026ThirdQuadrantCellRight k τ

/-- Containment is equivalent to the explicit `T*j*log p` inequalities. -/
theorem cfzp026PrimePowerCenteredAngleContained_iff_quantitativeHit
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j k : ℕ) (τ : ℝ) :
    Cfzp026PrimePowerCenteredAngleContainedInThirdQuadrantCell ε W p j k τ ↔
      Cfzp026PrimePowerQuantitativeThirdQuadrantHit ε W p j k τ := by
  rw [cfzp026PrimePowerCenteredAngleContained_iff_center_halfWidth]
  unfold Cfzp026PrimePowerQuantitativeThirdQuadrantHit
    cfzpPrimePowerPhaseAngleHalfWidth
  rw [cfzpPrimePowerPhaseAngle_center_eq_T_mul_primePowerCenter]

/-- Any point of a centered open angle interval lies in the containing cell. -/
theorem cfzp026_mem_thirdQuadrantCell_of_centeredAngle_mem
    {ε : ℝ} {W : PascalCenteredXiResidueTransportWindow}
    {p j k : ℕ} {τ θ : ℝ}
    (hcontain : Cfzp026PrimePowerCenteredAngleContainedInThirdQuadrantCell
      ε W p j k τ)
    (hθ : θ ∈ Set.Ioo
      (cfzpPrimePowerPhaseAngleLeft ε W p j)
      (cfzpPrimePowerPhaseAngleRight ε W p j)) :
    θ ∈ Set.Icc
      (cfzp026ThirdQuadrantCellLeft k τ)
      (cfzp026ThirdQuadrantCellRight k τ) := by
  exact ⟨hcontain.1.trans hθ.1.le, hθ.2.le.trans hcontain.2⟩

/-! ## Gate E: endpoint coefficient floors -/

/-- Lower floor for the coefficient multiplying `sin θ`. -/
noncomputable def cfzp026PhaseSinCoeffFloor (α L R : ℝ) : ℝ :=
  L ^ 2 * (1 - α ^ 2) - 2 * (α * R + 1)

/-- Lower floor for the coefficient multiplying `cos θ`. -/
noncomputable def cfzp026PhaseCosCoeffFloor (α L : ℝ) : ℝ :=
  2 * L * (α * L + 1)

/-- The sine coefficient is bounded below by its cell endpoint floor. -/
theorem cfzp026PhaseSinCoeffFloor_le
    {α L R θ : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hL0 : 0 ≤ L) (hLθ : L ≤ θ) (hθR : θ ≤ R) :
    cfzp026PhaseSinCoeffFloor α L R ≤
      cfzpPhaseDerivativeSinCoeff α θ := by
  have hθ0 : 0 ≤ θ := hL0.trans hLθ
  have hquad : L ^ 2 ≤ θ ^ 2 := by
    have h := mul_nonneg (sub_nonneg.mpr hLθ) (add_nonneg hL0 hθ0)
    nlinarith
  have hcoef : 0 ≤ 1 - α ^ 2 := by
    have h := mul_nonneg hα0 (sub_nonneg.mpr hα1)
    nlinarith
  have hterm : L ^ 2 * (1 - α ^ 2) ≤
      θ ^ 2 * (1 - α ^ 2) :=
    mul_le_mul_of_nonneg_right hquad hcoef
  have hαθR : α * θ ≤ α * R :=
    mul_le_mul_of_nonneg_left hθR hα0
  unfold cfzp026PhaseSinCoeffFloor cfzpPhaseDerivativeSinCoeff
  nlinarith

/-- The cosine coefficient is bounded below by its left endpoint floor. -/
theorem cfzp026PhaseCosCoeffFloor_le
    {α L θ : ℝ} (hα0 : 0 ≤ α) (hL0 : 0 ≤ L) (hLθ : L ≤ θ) :
    cfzp026PhaseCosCoeffFloor α L ≤
      2 * θ * (α * θ + 1) := by
  have hθ0 : 0 ≤ θ := hL0.trans hLθ
  have hquad : L ^ 2 ≤ θ ^ 2 := by
    have h := mul_nonneg (sub_nonneg.mpr hLθ) (add_nonneg hL0 hθ0)
    nlinarith
  have hαquad : 0 ≤ α * (θ ^ 2 - L ^ 2) :=
    mul_nonneg hα0 (sub_nonneg.mpr hquad)
  have hdiff : 0 ≤ θ - L := sub_nonneg.mpr hLθ
  unfold cfzp026PhaseCosCoeffFloor
  nlinarith

/-- The cosine floor is strictly positive at a positive left endpoint. -/
theorem cfzp026PhaseCosCoeffFloor_pos
    {α L : ℝ} (hα0 : 0 ≤ α) (hL : 0 < L) :
    0 < cfzp026PhaseCosCoeffFloor α L := by
  unfold cfzp026PhaseCosCoeffFloor
  have hαL : 0 ≤ α * L := mul_nonneg hα0 hL.le
  nlinarith

/-! ## Gate F: explicit phase-core margin -/

/-- The explicit phase-core credit supplied by a trimmed periodic cell. -/
noncomputable def cfzp026PhaseCoreMargin
    (α : ℝ) (k : ℕ) (τ : ℝ) : ℝ :=
  (cfzp026PhaseSinCoeffFloor α
      (cfzp026ThirdQuadrantCellLeft k τ)
      (cfzp026ThirdQuadrantCellRight k τ) +
    cfzp026PhaseCosCoeffFloor α
      (cfzp026ThirdQuadrantCellLeft k τ)) * Real.sin τ

/-- The cell margin is nonnegative under the endpoint-floor condition. -/
theorem cfzp026PhaseCoreMargin_nonneg
    {α : ℝ} {k : ℕ} {τ : ℝ} (hα : 0 ≤ α) (hτ : 0 ≤ τ)
    (hτ4 : τ ≤ Real.pi / 4)
    (hA : 0 ≤ cfzp026PhaseSinCoeffFloor α
      (cfzp026ThirdQuadrantCellLeft k τ)
      (cfzp026ThirdQuadrantCellRight k τ)) :
    0 ≤ cfzp026PhaseCoreMargin α k τ := by
  have hL : 0 ≤ cfzp026ThirdQuadrantCellLeft k τ :=
    (cfzp026ThirdQuadrantCellLeft_pos hτ).le
  have hB : 0 ≤ cfzp026PhaseCosCoeffFloor α
      (cfzp026ThirdQuadrantCellLeft k τ) := by
    unfold cfzp026PhaseCosCoeffFloor
    have hαL : 0 ≤ α * cfzp026ThirdQuadrantCellLeft k τ :=
      mul_nonneg hα hL
    nlinarith
  have hsin : 0 ≤ Real.sin τ := by
    apply Real.sin_nonneg_of_mem_Icc
    constructor
    · exact hτ
    · nlinarith [hτ4, Real.pi_pos]
  exact mul_nonneg (add_nonneg hA hB) hsin

/-- A strictly trimmed cell supplies a strictly positive phase-core margin. -/
theorem cfzp026PhaseCoreMargin_pos
    {α : ℝ} {k : ℕ} {τ : ℝ} (hα : 0 ≤ α) (hτ : 0 < τ)
    (hτ4 : τ ≤ Real.pi / 4)
    (hA : 0 ≤ cfzp026PhaseSinCoeffFloor α
      (cfzp026ThirdQuadrantCellLeft k τ)
      (cfzp026ThirdQuadrantCellRight k τ)) :
    0 < cfzp026PhaseCoreMargin α k τ := by
  have hL := cfzp026ThirdQuadrantCellLeft_pos (k := k) hτ.le
  have hB := cfzp026PhaseCosCoeffFloor_pos hα hL
  have hsin : 0 < Real.sin τ :=
    Real.sin_pos_of_pos_of_lt_pi hτ (by nlinarith [hτ4, Real.pi_pos])
  unfold cfzp026PhaseCoreMargin
  exact mul_pos (add_pos_of_nonneg_of_pos hA hB) hsin

/-- Cell containment supplies the CFZP-025 uniform phase-core margin. -/
theorem cfzp026CenteredPhaseCoreNegativeMargin_of_cellContainment
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    {p j k : ℕ} {τ : ℝ} (hτ : 0 < τ) (hτ4 : τ ≤ Real.pi / 4)
    (hα1 : cfzpModePhaseAspectRatio W ≤ 1)
    (hA : 0 ≤ cfzp026PhaseSinCoeffFloor
      (cfzpModePhaseAspectRatio W)
      (cfzp026ThirdQuadrantCellLeft k τ)
      (cfzp026ThirdQuadrantCellRight k τ))
    (hcontain : Cfzp026PrimePowerCenteredAngleContainedInThirdQuadrantCell
      ε W p j k τ) :
    Cfzp025CenteredPhaseCoreNegativeMargin ε W p j
      (cfzp026PhaseCoreMargin (cfzpModePhaseAspectRatio W) k τ) := by
  intro θ hθ
  have hcell := cfzp026_mem_thirdQuadrantCell_of_centeredAngle_mem
    hcontain hθ
  have hLpos := cfzp026ThirdQuadrantCellLeft_pos (k := k) hτ.le
  have hα0 := (cfzpModePhaseAspectRatio_pos W).le
  have hAfloor := cfzp026PhaseSinCoeffFloor_le hα0 hα1
    hLpos.le hcell.1 hcell.2
  have hBfloor := cfzp026PhaseCosCoeffFloor_le hα0 hLpos.le hcell.1
  have htrig := cfzp026_sin_cos_le_neg_sin_of_mem_thirdQuadrantCell
    hτ.le hτ4 hcell
  have hsin : 0 ≤ Real.sin τ := by
    exact (Real.sin_pos_of_pos_of_lt_pi hτ
      (by nlinarith [hτ4, Real.pi_pos])).le
  have hcore := cfzp025PhaseDerivativeCore_le_neg_of_quantitativeThirdQuadrantCell
    hA hAfloor hsin htrig.1
      (by
        have hB := cfzp026PhaseCosCoeffFloor_pos hα0 hLpos
        exact hB.le)
      hBfloor hsin htrig.2
  calc
    cfzpPhaseDerivativeCore (cfzpModePhaseAspectRatio W) θ ≤
        -(cfzp026PhaseSinCoeffFloor (cfzpModePhaseAspectRatio W)
          (cfzp026ThirdQuadrantCellLeft k τ)
          (cfzp026ThirdQuadrantCellRight k τ) * Real.sin τ +
          cfzp026PhaseCosCoeffFloor (cfzpModePhaseAspectRatio W)
            (cfzp026ThirdQuadrantCellLeft k τ) * Real.sin τ) := hcore
    _ = -cfzp026PhaseCoreMargin (cfzpModePhaseAspectRatio W) k τ := by
      unfold cfzp026PhaseCoreMargin
      ring

/-! ## Gate G: event and pulse credit -/

/-- A periodic cell hit gives the CFZP-025 event credit directly. -/
theorem cfzp026PrimePowerBranchFreeTrigEvent_ge_phaseCoreCredit_of_cellContainment
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j k : ℕ} (hp : Nat.Prime p) (hj : 0 < j) {τ : ℝ}
    (hτ : 0 < τ) (hτ4 : τ ≤ Real.pi / 4)
    (hα1 : cfzpModePhaseAspectRatio W ≤ 1)
    (hA : 0 ≤ cfzp026PhaseSinCoeffFloor
      (cfzpModePhaseAspectRatio W)
      (cfzp026ThirdQuadrantCellLeft k τ)
      (cfzp026ThirdQuadrantCellRight k τ))
    (hcontain : Cfzp026PrimePowerCenteredAngleContainedInThirdQuadrantCell
      ε W p j k τ) :
    2 * Real.log (p : ℝ) * cfzpModeCriticalScale (p ^ j) *
        (cfzp025CenteredDerivativePrefactorFloor ε W p j *
          cfzp026PhaseCoreMargin (cfzpModePhaseAspectRatio W) k τ) ≤
      cfzpPrimePowerBranchFreeTrigEvent ε W p j := by
  exact cfzp025PrimePowerBranchFreeTrigEvent_ge_phaseCoreCredit
    hε hε2 W hp hj
    (cfzp026PhaseCoreMargin_nonneg
      (cfzpModePhaseAspectRatio_pos W).le hτ.le hτ4 hA)
    (cfzp026CenteredPhaseCoreNegativeMargin_of_cellContainment W
      hτ hτ4 hα1 hA hcontain)

/-- The same periodic-cell credit transports to the von Mangoldt pulse. -/
theorem cfzp026VonMangoldtPulse_ge_phaseCoreCredit_of_cellContainment
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j n k : ℕ} (hp : Nat.Prime p) (hj : 0 < j) (hn : n = p ^ j)
    {τ : ℝ} (hτ : 0 < τ) (hτ4 : τ ≤ Real.pi / 4)
    (hα1 : cfzpModePhaseAspectRatio W ≤ 1)
    (hA : 0 ≤ cfzp026PhaseSinCoeffFloor
      (cfzpModePhaseAspectRatio W)
      (cfzp026ThirdQuadrantCellLeft k τ)
      (cfzp026ThirdQuadrantCellRight k τ))
    (hcontain : Cfzp026PrimePowerCenteredAngleContainedInThirdQuadrantCell
      ε W p j k τ) :
    2 * Real.log (p : ℝ) * cfzpModeCriticalScale (p ^ j) *
        (cfzp025CenteredDerivativePrefactorFloor ε W p j *
          cfzp026PhaseCoreMargin (cfzpModePhaseAspectRatio W) k τ) ≤
      cfzp021VonMangoldtPulse ε W n := by
  rw [hn, cfzp021VonMangoldtPulse_eq_branchFreeTrigEvent_of_eq_prime_pow
    hε hε2 W hp hj rfl]
  exact cfzp026PrimePowerBranchFreeTrigEvent_ge_phaseCoreCredit_of_cellContainment
    hε hε2 W hp hj hτ hτ4 hα1 hA hcontain

/-! ## Gate H: periodic-cell Good data and CFZP-024 -/

private theorem cfzp026_prime_and_positive_exponent
    {A B : ℕ} (hAB : A ≤ B) {pk : ℕ × ℕ}
    (hpk : pk ∈ cfzp024PrimePowerPairBlockSupport A B) :
    Nat.Prime pk.1 ∧ 0 < pk.2 + 1 := by
  have hs := mem_pascalPrimePowerPairSupportUpTo_iff.mp
    (cfzp024PrimePowerPairBlockSupport_subset_right hAB hpk)
  exact ⟨(mem_pascalPrimeCoordinateSupportUpTo_iff.mp hs.1).1, by omega⟩

/-- Build a CFZP-024 certificate from periodic third-quadrant Good hits.
The only remaining Bad-side inputs are the explicit absolute derivative
envelope and credit/debt data already required by CFZP-024. -/
noncomputable def cfzp026FiniteBlockCertificate_of_periodicThirdQuadrantCellHits
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B)
    (Good : Finset (ℕ × ℕ))
    (hGood : Good ⊆ cfzp024PrimePowerPairBlockSupport A B)
    (k : ℕ × ℕ → ℕ) (τ : ℕ × ℕ → ℝ)
    (hτ : ∀ pk ∈ Good, 0 < τ pk)
    (hτ4 : ∀ pk ∈ Good, τ pk ≤ Real.pi / 4)
    (hα1 : cfzpModePhaseAspectRatio W ≤ 1)
    (hA : ∀ pk ∈ Good, 0 ≤ cfzp026PhaseSinCoeffFloor
      (cfzpModePhaseAspectRatio W)
      (cfzp026ThirdQuadrantCellLeft (k pk) (τ pk))
      (cfzp026ThirdQuadrantCellRight (k pk) (τ pk)))
    (hcontain : ∀ pk ∈ Good,
      Cfzp026PrimePowerCenteredAngleContainedInThirdQuadrantCell ε W
        pk.1 (pk.2 + 1) (k pk) (τ pk))
    (K : ℕ × ℕ → ℝ)
    (hK : ∀ pk ∈ cfzp024BadPrimePowerPairBlockSupport A B Good, 0 ≤ K pk)
    (henvelope : ∀ pk ∈ cfzp024BadPrimePowerPairBlockSupport A B Good,
      Cfzp023CenteredProfileDerivativeAbsEnvelope ε W pk.1 (pk.2 + 1) (K pk)) :
    Cfzp024FiniteBlockCertificate ε W A B := by
  let δ : ℕ × ℕ → ℝ := fun pk =>
    cfzp026PhaseCoreMargin (cfzpModePhaseAspectRatio W) (k pk) (τ pk)
  refine cfzp025FiniteBlockCertificate_of_phaseCoreMargins
    hε hε2 W hAB Good hGood δ ?_ ?_ K hK henvelope
  · intro pk hpk
    exact cfzp026PhaseCoreMargin_nonneg
      (cfzpModePhaseAspectRatio_pos W).le (hτ pk hpk).le
        (hτ4 pk hpk) (hA pk hpk)
  · intro pk hpk
    exact cfzp026CenteredPhaseCoreNegativeMargin_of_cellContainment W
      (hτ pk hpk) (hτ4 pk hpk) hα1 (hA pk hpk) (hcontain pk hpk)

/-! ## Gate J: provider firewall -/

/-- No cofinal quantitative prime-power phase-hit provider is asserted here. -/
inductive Cfzp026PeriodicThirdQuadrantPhaseCellCertificateGap : Prop
  | noIndependentCofinalPrimePowerQuantitativeThirdQuadrantHitProvider

end DkMath.RH.CFBRCProjection
