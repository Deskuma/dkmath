/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaPeriodicThirdQuadrantPhaseCellCertificateAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaSubcriticalLargeCellCoefficientReadinessAudit"

/-!
# CFZP-027: subcritical large-cell coefficient readiness

This module removes the per-pair `A₀ ≥ 0` input from the CFZP-026 cell
certificate once a subcritical aspect ratio and an explicit large-cell
readiness contract are supplied.  It also records the exact width of the
prime-power center target.  The subcritical window hypothesis and all
prime-power phase-hit providers remain explicit; no density or cofinal-hit
theorem is asserted.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open Set

/-! ## Gate A: subcritical aspect ratio -/

/-- The structural hypothesis that the phase aspect ratio is subcritical. -/
def Cfzp027SubcriticalPhaseAspect
    (W : PascalCenteredXiResidueTransportWindow) : Prop :=
  cfzpModePhaseAspectRatio W < 1

/-- A subcritical aspect ratio is automatically at most one. -/
theorem cfzp027SubcriticalPhaseAspect_le_one
    {W : PascalCenteredXiResidueTransportWindow}
    (hα : Cfzp027SubcriticalPhaseAspect W) :
    cfzpModePhaseAspectRatio W ≤ 1 :=
  hα.le

/-- The subcritical hypothesis gives a positive quadratic coefficient. -/
theorem cfzp027_one_sub_aspect_sq_pos
    {W : PascalCenteredXiResidueTransportWindow}
    (hα : Cfzp027SubcriticalPhaseAspect W) :
    0 < 1 - (cfzpModePhaseAspectRatio W) ^ 2 := by
  change cfzpModePhaseAspectRatio W < 1 at hα
  have hα0 : 0 < cfzpModePhaseAspectRatio W :=
    cfzpModePhaseAspectRatio_pos W
  have hprod : 0 <
      (1 + cfzpModePhaseAspectRatio W) *
        (1 - cfzpModePhaseAspectRatio W) := by
    exact mul_pos (by linarith) (sub_pos.mpr hα)
  nlinarith

/-- The subcritical ratio can equivalently be stated as an abscissa bound. -/
theorem cfzp027SubcriticalPhaseAspect_iff_abscissa_lt_rectangleT
    (W : PascalCenteredXiResidueTransportWindow) :
    Cfzp027SubcriticalPhaseAspect W ↔
      cfzpModePhaseAbscissa W < W.rectangle.T := by
  unfold Cfzp027SubcriticalPhaseAspect cfzpModePhaseAspectRatio
  rw [div_lt_iff₀ W.rectangle.hT]
  simp

/-! ## Gate B: the untrimmed floor is worst -/

/-- The sine coefficient floor at the untrimmed periodic cell. -/
noncomputable def cfzp027UntrimmedPhaseSinCoeffFloor
    (α : ℝ) (k : ℕ) : ℝ :=
  cfzp026PhaseSinCoeffFloor α
    (cfzp026ThirdQuadrantCellLeft k 0)
    (cfzp026ThirdQuadrantCellRight k 0)

/-- Trimming a cell cannot lower the sine coefficient floor. -/
theorem cfzp027UntrimmedPhaseSinCoeffFloor_le_trimmed
    {α : ℝ} {k : ℕ} {τ : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hτ : 0 ≤ τ) :
    cfzp027UntrimmedPhaseSinCoeffFloor α k ≤
      cfzp026PhaseSinCoeffFloor α
        (cfzp026ThirdQuadrantCellLeft k τ)
        (cfzp026ThirdQuadrantCellRight k τ) := by
  have hL0 : 0 ≤ cfzp026ThirdQuadrantCellLeft k 0 :=
    (cfzp026ThirdQuadrantCellLeft_pos (k := k) (τ := 0) (by norm_num)).le
  have hLL : cfzp026ThirdQuadrantCellLeft k 0 ≤
      cfzp026ThirdQuadrantCellLeft k τ := by
    unfold cfzp026ThirdQuadrantCellLeft
    nlinarith
  have hRR : cfzp026ThirdQuadrantCellRight k τ ≤
      cfzp026ThirdQuadrantCellRight k 0 := by
    unfold cfzp026ThirdQuadrantCellRight
    nlinarith
  have hLτ : 0 ≤ cfzp026ThirdQuadrantCellLeft k τ :=
    hL0.trans hLL
  have hquad :
      (cfzp026ThirdQuadrantCellLeft k 0) ^ 2 ≤
        (cfzp026ThirdQuadrantCellLeft k τ) ^ 2 := by
    have h := mul_nonneg (sub_nonneg.mpr hLL)
      (add_nonneg hL0 hLτ)
    nlinarith
  have hcoef : 0 ≤ 1 - α ^ 2 := by
    have h := mul_nonneg hα0 (sub_nonneg.mpr hα1)
    nlinarith
  have hterm := mul_le_mul_of_nonneg_right hquad hcoef
  have hαR : α * cfzp026ThirdQuadrantCellRight k τ ≤
      α * cfzp026ThirdQuadrantCellRight k 0 :=
    mul_le_mul_of_nonneg_left hRR hα0
  unfold cfzp027UntrimmedPhaseSinCoeffFloor
    cfzp026PhaseSinCoeffFloor
  nlinarith

/-! ## Gate C: explicit readiness contract -/

/-- A finite large-cell contract for the sine coefficient floor. -/
def Cfzp027PhaseSinCoefficientReady (α : ℝ) (k : ℕ) : Prop :=
  4 ≤ (1 - α ^ 2) * (2 * Real.pi * (k : ℝ)) ∧
  3 * Real.pi + 2 ≤ 2 * (2 * Real.pi * (k : ℝ))

/-- A ready untrimmed cell has a nonnegative sine coefficient floor. -/
theorem cfzp027UntrimmedPhaseSinCoeffFloor_nonneg_of_ready
    {α : ℝ} {k : ℕ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hready : Cfzp027PhaseSinCoefficientReady α k) :
    0 ≤ cfzp027UntrimmedPhaseSinCoeffFloor α k := by
  let x : ℝ := 2 * Real.pi * (k : ℝ)
  let d : ℝ := 1 - α ^ 2
  have hx : 0 ≤ x := by
    dsimp [x]
    positivity
  have hdx : 4 ≤ d * x := by
    simpa [d, x] using hready.1
  have hsecond : 3 * Real.pi + 2 ≤ 2 * x := by
    simpa [x] using hready.2
  have hLx : x ≤ cfzp026ThirdQuadrantCellLeft k 0 := by
    unfold cfzp026ThirdQuadrantCellLeft
    dsimp [x]
    nlinarith [Real.pi_pos]
  have hL0 : 0 ≤ cfzp026ThirdQuadrantCellLeft k 0 :=
    (cfzp026ThirdQuadrantCellLeft_pos (k := k) (τ := 0) (by norm_num)).le
  have hR0 : 0 ≤ cfzp026ThirdQuadrantCellRight k 0 := by
    unfold cfzp026ThirdQuadrantCellRight
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith [Real.pi_pos]
  have hquad : x ^ 2 ≤
      (cfzp026ThirdQuadrantCellLeft k 0) ^ 2 := by
    have h := mul_nonneg (sub_nonneg.mpr hLx)
      (add_nonneg hx hL0)
    nlinarith
  have hd : 0 < d := by
    dsimp [d]
    have hprod : 0 < (1 + α) * (1 - α) :=
      mul_pos (by linarith) (sub_pos.mpr hα1)
    nlinarith
  have hterm : d * x ^ 2 ≤ d *
      (cfzp026ThirdQuadrantCellLeft k 0) ^ 2 :=
    mul_le_mul_of_nonneg_left hquad hd.le
  have hdx2 : 4 * x ≤ d * x ^ 2 := by
    calc
      4 * x ≤ (d * x) * x :=
        mul_le_mul_of_nonneg_right hdx hx
      _ = d * x ^ 2 := by ring
  have hfour : 2 * x + 3 * Real.pi + 2 ≤ 4 * x := by
    nlinarith [hsecond]
  have hαR : α * cfzp026ThirdQuadrantCellRight k 0 ≤
      cfzp026ThirdQuadrantCellRight k 0 := by
    have h := mul_le_mul_of_nonneg_right hα1.le hR0
    simpa using h
  have hneg : 2 * (α * cfzp026ThirdQuadrantCellRight k 0 + 1) ≤
      2 * x + 3 * Real.pi + 2 := by
    unfold cfzp026ThirdQuadrantCellRight at hαR ⊢
    dsimp [x] at hαR ⊢
    nlinarith
  unfold cfzp027UntrimmedPhaseSinCoeffFloor
    cfzp026PhaseSinCoeffFloor
  nlinarith [hterm, hdx2, hfour, hneg]

/-! ## Gate D: readiness supplies every trimmed-cell condition -/

/-- Readiness supplies the `A₀ ≥ 0` input required by CFZP-026. -/
theorem cfzp027PhaseSinCoeffFloor_nonneg_of_ready
    {α : ℝ} {k : ℕ} {τ : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hτ : 0 ≤ τ) (hready : Cfzp027PhaseSinCoefficientReady α k) :
    0 ≤ cfzp026PhaseSinCoeffFloor α
      (cfzp026ThirdQuadrantCellLeft k τ)
      (cfzp026ThirdQuadrantCellRight k τ) := by
  exact (cfzp027UntrimmedPhaseSinCoeffFloor_nonneg_of_ready
    hα0 hα1 hready).trans
    (cfzp027UntrimmedPhaseSinCoeffFloor_le_trimmed
      hα0 hα1.le hτ)

/-! ## Gate E: sufficiently large cells are ready -/

/-- Every subcritical aspect ratio has an eventual readiness threshold. -/
theorem cfzp027_exists_eventually_ready_cellIndex
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    ∃ K₀ : ℕ, ∀ k : ℕ, K₀ ≤ k →
      Cfzp027PhaseSinCoefficientReady α k := by
  have hd : 0 < 1 - α ^ 2 := by
    have hprod : 0 < (1 + α) * (1 - α) :=
      mul_pos (by linarith) (sub_pos.mpr hα1)
    nlinarith
  have hx : Tendsto (fun k : ℕ => 2 * Real.pi * (k : ℝ)) atTop atTop := by
    simpa [mul_assoc] using
      (tendsto_natCast_atTop_atTop.const_mul_atTop
        (by positivity : 0 < 2 * Real.pi))
  have hfirst : Tendsto (fun k : ℕ =>
      (1 - α ^ 2) * (2 * Real.pi * (k : ℝ))) atTop atTop :=
    hx.const_mul_atTop hd
  have hsecond : Tendsto (fun k : ℕ =>
      2 * (2 * Real.pi * (k : ℝ))) atTop atTop :=
    hx.const_mul_atTop (by norm_num)
  have hev : ∀ᶠ k : ℕ in atTop,
      Cfzp027PhaseSinCoefficientReady α k := by
    filter_upwards [hfirst.eventually (eventually_ge_atTop (4 : ℝ)),
      hsecond.eventually (eventually_ge_atTop (3 * Real.pi + 2))]
      with k hk₁ hk₂
    exact ⟨hk₁, hk₂⟩
  rcases (eventually_atTop.1 hev) with ⟨K₀, hK₀⟩
  exact ⟨K₀, hK₀⟩

/-- A ready cell can be chosen above any prescribed finite index. -/
theorem cfzp027_exists_ready_cellIndex_ge
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (K : ℕ) :
    ∃ k : ℕ, K ≤ k ∧ Cfzp027PhaseSinCoefficientReady α k := by
  obtain ⟨K₀, hK₀⟩ := cfzp027_exists_eventually_ready_cellIndex hα0 hα1
  refine ⟨max K K₀, le_max_left _ _, hK₀ _ (le_max_right _ _)⟩

/-! ## Gate F: center-target width -/

/-- The open center target obtained after trimming both interval endpoints. -/
def Cfzp027ThirdQuadrantTargetHasInterior
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (τ : ℝ) : Prop :=
  τ + W.rectangle.T * ε < Real.pi / 4

/-- The exact width of the admissible prime-power center target. -/
theorem cfzp027ThirdQuadrantCenterTarget_width
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (k : ℕ) (τ : ℝ) :
    (cfzp026ThirdQuadrantCellRight k τ - W.rectangle.T * ε) -
        (cfzp026ThirdQuadrantCellLeft k τ + W.rectangle.T * ε) =
      Real.pi / 2 - 2 * τ - 2 * W.rectangle.T * ε := by
  unfold cfzp026ThirdQuadrantCellRight cfzp026ThirdQuadrantCellLeft
  ring

/-- The target has positive width exactly when its trim is below `π/4`. -/
theorem cfzp027ThirdQuadrantTargetHasInterior_iff_width_pos
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (τ : ℝ) :
    0 < Real.pi / 2 - 2 * τ - 2 * W.rectangle.T * ε ↔
      Cfzp027ThirdQuadrantTargetHasInterior ε W τ := by
  unfold Cfzp027ThirdQuadrantTargetHasInterior
  constructor <;> intro h <;> nlinarith

/-! ## Gate G: ready arithmetic hits -/

/-- A finite hit together with the automatic large-cell readiness contract. -/
def Cfzp027PrimePowerReadyThirdQuadrantHit
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j k : ℕ) (τ : ℝ) : Prop :=
  Cfzp026PrimePowerQuantitativeThirdQuadrantHit ε W p j k τ ∧
    Cfzp027PhaseSinCoefficientReady
      (cfzpModePhaseAspectRatio W) k

/-- A ready hit supplies CFZP-026 cell containment without an `A₀` input. -/
theorem cfzp027_containment_of_ready_hit
    {ε : ℝ} {W : PascalCenteredXiResidueTransportWindow}
    {p j k : ℕ} {τ : ℝ}
    (hhit : Cfzp027PrimePowerReadyThirdQuadrantHit ε W p j k τ) :
    Cfzp026PrimePowerCenteredAngleContainedInThirdQuadrantCell
      ε W p j k τ :=
  cfzp026PrimePowerCenteredAngleContained_iff_quantitativeHit ε W p j k τ |>.2 hhit.1

/-- A subcritical ready hit yields a strictly positive phase-core margin. -/
theorem cfzp027PhaseCoreMargin_pos_of_subcritical_ready_hit
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    {p j k : ℕ} {τ : ℝ}
    (hsub : Cfzp027SubcriticalPhaseAspect W) (hτ : 0 < τ)
    (hτ4 : τ ≤ Real.pi / 4)
    (hhit : Cfzp027PrimePowerReadyThirdQuadrantHit ε W p j k τ) :
    0 < cfzp026PhaseCoreMargin
      (cfzpModePhaseAspectRatio W) k τ := by
  exact cfzp026PhaseCoreMargin_pos
    (cfzpModePhaseAspectRatio_pos W).le hτ hτ4
    (cfzp027PhaseSinCoeffFloor_nonneg_of_ready
      (cfzpModePhaseAspectRatio_pos W).le hsub hτ.le hhit.2)

/-! ## Gate H: direct event/pulse credit -/

/-- A subcritical ready hit gives explicit positive event credit. -/
theorem cfzp027PrimePowerBranchFreeTrigEvent_ge_readyPhaseCoreCredit
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j k : ℕ} (hp : Nat.Prime p) (hj : 0 < j) {τ : ℝ}
    (hsub : Cfzp027SubcriticalPhaseAspect W) (hτ : 0 < τ)
    (hτ4 : τ ≤ Real.pi / 4)
    (hhit : Cfzp027PrimePowerReadyThirdQuadrantHit ε W p j k τ) :
    2 * Real.log (p : ℝ) * cfzpModeCriticalScale (p ^ j) *
        (cfzp025CenteredDerivativePrefactorFloor ε W p j *
          cfzp026PhaseCoreMargin (cfzpModePhaseAspectRatio W) k τ) ≤
      cfzpPrimePowerBranchFreeTrigEvent ε W p j := by
  have hA := cfzp027PhaseSinCoeffFloor_nonneg_of_ready
    (cfzpModePhaseAspectRatio_pos W).le hsub hτ.le hhit.2
  exact cfzp026PrimePowerBranchFreeTrigEvent_ge_phaseCoreCredit_of_cellContainment
    hε hε2 W hp hj hτ hτ4 hsub.le hA
    (cfzp027_containment_of_ready_hit hhit)

/-- The ready-hit event credit transports to the von Mangoldt pulse. -/
theorem cfzp027VonMangoldtPulse_ge_readyPhaseCoreCredit
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j n k : ℕ} (hp : Nat.Prime p) (hj : 0 < j) (hn : n = p ^ j)
    {τ : ℝ} (hsub : Cfzp027SubcriticalPhaseAspect W) (hτ : 0 < τ)
    (hτ4 : τ ≤ Real.pi / 4)
    (hhit : Cfzp027PrimePowerReadyThirdQuadrantHit ε W p j k τ) :
    2 * Real.log (p : ℝ) * cfzpModeCriticalScale (p ^ j) *
        (cfzp025CenteredDerivativePrefactorFloor ε W p j *
          cfzp026PhaseCoreMargin (cfzpModePhaseAspectRatio W) k τ) ≤
      cfzp021VonMangoldtPulse ε W n := by
  rw [hn, cfzp021VonMangoldtPulse_eq_branchFreeTrigEvent_of_eq_prime_pow
    hε hε2 W hp hj rfl]
  exact cfzp027PrimePowerBranchFreeTrigEvent_ge_readyPhaseCoreCredit
    hε hε2 W hp hj hsub hτ hτ4 hhit

/-! ## Gate I: CFZP-024 constructor without per-pair `A₀` -/

/-- Build a CFZP-024 certificate from subcritical ready Good hits. -/
noncomputable def cfzp027FiniteBlockCertificate_of_subcriticalReadyHits
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B)
    (Good : Finset (ℕ × ℕ))
    (hGood : Good ⊆ cfzp024PrimePowerPairBlockSupport A B)
    (k : ℕ × ℕ → ℕ) (τ : ℕ × ℕ → ℝ)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (hτ : ∀ pk ∈ Good, 0 < τ pk)
    (hτ4 : ∀ pk ∈ Good, τ pk ≤ Real.pi / 4)
    (hready : ∀ pk ∈ Good,
      Cfzp027PrimePowerReadyThirdQuadrantHit ε W
        pk.1 (pk.2 + 1) (k pk) (τ pk))
    (K : ℕ × ℕ → ℝ)
    (hK : ∀ pk ∈ cfzp024BadPrimePowerPairBlockSupport A B Good, 0 ≤ K pk)
    (henvelope : ∀ pk ∈ cfzp024BadPrimePowerPairBlockSupport A B Good,
      Cfzp023CenteredProfileDerivativeAbsEnvelope ε W pk.1 (pk.2 + 1) (K pk)) :
    Cfzp024FiniteBlockCertificate ε W A B := by
  refine cfzp026FiniteBlockCertificate_of_periodicThirdQuadrantCellHits
    hε hε2 W hAB Good hGood k τ hτ hτ4 hsub.le ?_ ?_ K hK henvelope
  · intro pk hpk
    exact cfzp027PhaseSinCoeffFloor_nonneg_of_ready
      (cfzpModePhaseAspectRatio_pos W).le hsub (hτ pk hpk).le
        (hready pk hpk).2
  · intro pk hpk
    exact cfzp027_containment_of_ready_hit (hready pk hpk)

/-! ## Gate J: next arithmetic/dynamical frontier -/

/-- The cofinal ready-hit provider required by the next rotation stage. -/
def Cfzp027CofinalReadyThirdQuadrantHitsForPrime
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p : ℕ) (τ : ℝ) : Prop :=
  ∀ J K : ℕ, ∃ j k : ℕ,
    J ≤ j ∧ K ≤ k ∧
      Cfzp027PrimePowerReadyThirdQuadrantHit ε W p j k τ

/-! ## Firewall -/

/-- No independent cofinal ready prime-power hit provider is asserted. -/
inductive Cfzp027SubcriticalLargeCellCoefficientReadinessGap : Prop
  | noIndependentCofinalReadyPrimePowerThirdQuadrantHitProvider

end DkMath.RH.CFBRCProjection
