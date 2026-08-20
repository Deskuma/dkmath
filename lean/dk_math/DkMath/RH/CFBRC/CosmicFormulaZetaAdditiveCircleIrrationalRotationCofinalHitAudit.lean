/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaSubcriticalLargeCellCoefficientReadinessAudit
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaAdditiveCircleIrrationalRotationCofinalHitAudit"

/-!
# CFZP-028: additive-circle irrational rotation and cofinal hits

This module makes the fixed-prime phase step an additive-circle rotation.  An
irrationality hypothesis gives a dense natural orbit by combining the existing
`AddCircle` irrational-rotation theorem with the compact-group
`denseRange_zsmul_iff_nsmul` bridge.  The remaining arithmetic conclusion is
then an exact lift through the open fundamental-period chart.

The irrationality and subcritical-window assumptions are intentionally
explicit.  In particular, this file does not manufacture an irrationality
proof for an arbitrary rectangle or a prime-phase provider.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open Set
open scoped Topology

/-! ## Gate A: the fixed-prime rotation step -/

/-- The phase increment contributed by one exponent at a fixed prime. -/
noncomputable def cfzp028PrimePhaseRotationStep
    (W : PascalCenteredXiResidueTransportWindow) (p : ℕ) : ℝ :=
  W.rectangle.T * Real.log (p : ℝ)

/-- The arithmetic hypothesis needed for irrational rotation modulo `2π`. -/
def Cfzp028PrimePhaseRotationIrrational
    (W : PascalCenteredXiResidueTransportWindow) (p : ℕ) : Prop :=
  Irrational (cfzp028PrimePhaseRotationStep W p / (2 * Real.pi))

/-- The phase center is the natural multiple of the fixed-prime step. -/
theorem cfzp028PrimePowerPhaseAngleCenter_eq_natMul_rotationStep
    (W : PascalCenteredXiResidueTransportWindow) (p j : ℕ) :
    cfzpPrimePowerPhaseAngleCenter W p j =
      (j : ℝ) * cfzp028PrimePhaseRotationStep W p := by
  unfold cfzpPrimePowerPhaseAngleCenter cfzp028PrimePhaseRotationStep
    cfzpPrimePowerPhaseCenter
  ring

/-- A prime gives a positive phase step. -/
theorem cfzp028PrimePhaseRotationStep_pos
    (W : PascalCenteredXiResidueTransportWindow)
    {p : ℕ} (hp : Nat.Prime p) :
    0 < cfzp028PrimePhaseRotationStep W p := by
  unfold cfzp028PrimePhaseRotationStep
  exact mul_pos W.rectangle.hT (Real.log_pos (by exact_mod_cast hp.one_lt))

/-! ## Gate B: density of the natural orbit -/

/-- Irrational rotation gives a dense natural orbit on `AddCircle (2π)`. -/
theorem cfzp028_denseRange_nsmul_primePhaseRotation
    (W : PascalCenteredXiResidueTransportWindow) {p : ℕ}
    (hirr : Cfzp028PrimePhaseRotationIrrational W p) :
    DenseRange (fun j : ℕ =>
      j • (↑(cfzp028PrimePhaseRotationStep W p) : AddCircle (2 * Real.pi))) := by
  letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  have hz : DenseRange (fun z : ℤ =>
      z • (↑(cfzp028PrimePhaseRotationStep W p) : AddCircle (2 * Real.pi))) := by
    exact (AddCircle.denseRange_zsmul_coe_iff).2 hirr
  exact (denseRange_zsmul_iff_nsmul).mp hz

/-! ## Gate C: the fundamental third-quadrant target -/

/-- The left endpoint of the first-period trimmed center target. -/
noncomputable def cfzp028TargetLeft
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (τ : ℝ) : ℝ :=
  Real.pi + τ + W.rectangle.T * ε

/-- The right endpoint of the first-period trimmed center target. -/
noncomputable def cfzp028TargetRight
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (τ : ℝ) : ℝ :=
  3 * Real.pi / 2 - τ - W.rectangle.T * ε

/-- The target endpoints have positive width under CFZP-027 interior. -/
theorem cfzp028TargetLeft_lt_right
    {ε : ℝ} {W : PascalCenteredXiResidueTransportWindow} {τ : ℝ}
    (hinterior : Cfzp027ThirdQuadrantTargetHasInterior ε W τ) :
    cfzp028TargetLeft ε W τ < cfzp028TargetRight ε W τ := by
  unfold cfzp028TargetLeft cfzp028TargetRight
  unfold Cfzp027ThirdQuadrantTargetHasInterior at hinterior
  nlinarith [Real.pi_pos]

/-- Positive trim parameters place the target strictly inside `(0, 2π)`. -/
theorem cfzp028Target_mem_Ioo_period
    {ε τ : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    (hε : 0 < ε) (hτ : 0 < τ)
    (_hinterior : Cfzp027ThirdQuadrantTargetHasInterior ε W τ) :
    Set.Ioo (cfzp028TargetLeft ε W τ) (cfzp028TargetRight ε W τ) ⊆
      Set.Ioo (0 : ℝ) (2 * Real.pi) := by
  intro x hx
  unfold cfzp028TargetLeft cfzp028TargetRight at *
  have hTe : 0 < W.rectangle.T * ε := mul_pos W.rectangle.hT hε
  have hxL := hx.1
  have hxR := hx.2
  constructor <;> nlinarith [Real.pi_pos, hTe, hτ, hxL, hxR]

/-- The quotient image of the real target window on the additive circle. -/
def cfzp028TargetCircle
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (τ : ℝ) :
    Set (AddCircle (2 * Real.pi)) :=
  ((↑) : ℝ → AddCircle (2 * Real.pi)) ''
    Set.Ioo (cfzp028TargetLeft ε W τ) (cfzp028TargetRight ε W τ)

/-- The target image is open whenever it lies in the fundamental chart. -/
theorem cfzp028TargetCircle_isOpen
    {ε τ : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    (hε : 0 < ε) (hτ : 0 < τ)
    (hinterior : Cfzp027ThirdQuadrantTargetHasInterior ε W τ) :
    IsOpen (cfzp028TargetCircle ε W τ) := by
  letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  change IsOpen ((AddCircle.openPartialHomeomorphCoe (2 * Real.pi) 0) '' _)
  apply OpenPartialHomeomorph.isOpen_image_of_subset_source
  · exact isOpen_Ioo
  · intro x hx
    change x ∈ Set.Ioo (0 : ℝ) (0 + 2 * Real.pi)
    simpa only [zero_add] using
      (cfzp028Target_mem_Ioo_period W hε hτ hinterior hx)

/-- The quotient target is nonempty under the strict width condition. -/
theorem cfzp028TargetCircle_nonempty
    {ε τ : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    (hinterior : Cfzp027ThirdQuadrantTargetHasInterior ε W τ) :
    (cfzp028TargetCircle ε W τ).Nonempty := by
  letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  unfold cfzp028TargetCircle
  have hlt := cfzp028TargetLeft_lt_right hinterior
  let x := (cfzp028TargetLeft ε W τ + cfzp028TargetRight ε W τ) / 2
  have hx : x ∈ Set.Ioo (cfzp028TargetLeft ε W τ)
      (cfzp028TargetRight ε W τ) := by
    dsimp [x]
    constructor <;> linarith
  refine ⟨(x : AddCircle (2 * Real.pi)), ?_⟩
  exact ⟨x, hx, rfl⟩

/-! ## Gate D: late natural hits -/

/-- A dense natural orbit hits every nonempty open set after any cutoff. -/
theorem cfzp028_exists_natMul_mem_open_ge
    {G : Type*} [TopologicalSpace G] [AddCommGroup G]
    [ContinuousAdd G] {a : G}
    (hdense : DenseRange (fun n : ℕ => n • a))
    {U : Set G} (hUo : IsOpen U) (hUne : U.Nonempty) (J : ℕ) :
    ∃ j : ℕ, J ≤ j ∧ j • a ∈ U := by
  let V : Set G := (fun x => J • a + x) ⁻¹' U
  have hVo : IsOpen V := hUo.preimage (continuous_const.add continuous_id)
  obtain ⟨u, hu⟩ := hUne
  have hVne : V.Nonempty := by
    refine ⟨u - J • a, ?_⟩
    dsimp [V]
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      using hu
  obtain ⟨n, hn⟩ := hdense.exists_mem_open hVo hVne
  refine ⟨J + n, Nat.le_add_right J n, ?_⟩
  simpa [V, add_nsmul, add_assoc, add_left_comm, add_comm] using hn

/-! ## Gate E: lift a circle hit to a periodic cell -/

/-- A circle target hit supplies the corresponding quantitative cell hit. -/
theorem cfzp028_quantitativeHit_of_targetCircle_mem
    {ε τ : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ}
    (hε : 0 < ε) (hτ : 0 < τ)
    (hinterior : Cfzp027ThirdQuadrantTargetHasInterior ε W τ)
    (hstep : 0 < cfzp028PrimePhaseRotationStep W p)
    (hmem : j • (↑(cfzp028PrimePhaseRotationStep W p) :
      AddCircle (2 * Real.pi)) ∈ cfzp028TargetCircle ε W τ) :
    ∃ k : ℕ, Cfzp026PrimePowerQuantitativeThirdQuadrantHit ε W p j k τ := by
  change (j • (↑(cfzp028PrimePhaseRotationStep W p) :
      AddCircle (2 * Real.pi))) ∈
      ((↑) : ℝ → AddCircle (2 * Real.pi)) '' _ at hmem
  obtain ⟨r, hr, hreq⟩ := hmem
  let x : ℝ := (j : ℝ) * cfzp028PrimePhaseRotationStep W p
  have hcoe : (x : AddCircle (2 * Real.pi)) = (r : AddCircle (2 * Real.pi)) := by
    calc
      (x : AddCircle (2 * Real.pi)) =
          j • (↑(cfzp028PrimePhaseRotationStep W p) :
            AddCircle (2 * Real.pi)) := by
        dsimp [x]
        rw [← AddCircle.coe_nsmul]
        simp [nsmul_eq_mul]
      _ = (r : AddCircle (2 * Real.pi)) := hreq.symm
  have hz0 : ((x - r : ℝ) : AddCircle (2 * Real.pi)) = 0 := by
    rw [AddCircle.coe_sub, hcoe, sub_self]
  obtain ⟨z : ℤ, hz⟩ := (AddCircle.coe_eq_zero_iff (2 * Real.pi)).mp hz0
  let q : ℤ := z
  have hxq : x = r + (q : ℝ) * (2 * Real.pi) := by
    have hz' : (z : ℝ) * (2 * Real.pi) = x - r := by
      simpa [smul_eq_mul] using hz
    calc
      x = r + (z : ℝ) * (2 * Real.pi) := by linarith [hz']
      _ = r + (q : ℝ) * (2 * Real.pi) := by rfl
  have hxpos : 0 ≤ x := by
    dsimp [x]
    exact mul_nonneg (Nat.cast_nonneg _) hstep.le
  have hq0 : 0 ≤ q := by
    by_contra hq
    have hq' : q ≤ -1 := by omega
    have hP : 0 < 2 * Real.pi := by positivity
    have hrP : r < 2 * Real.pi := by
      have := cfzp028Target_mem_Ioo_period W hε hτ hinterior hr
      exact this.2
    have hqR : (q : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast hq'
    have hqP := mul_le_mul_of_nonneg_right hqR hP.le
    have hxneg : x < 0 := by
      nlinarith [hxq, hr.1, hqP, hrP]
    exact (not_lt_of_ge hxpos) hxneg
  let k' : ℕ := q.toNat
  have hqcast : (q : ℝ) = (k' : ℝ) := by
    dsimp [k']
    exact_mod_cast (Int.toNat_of_nonneg hq0).symm
  have hxq' : x = r + (k' : ℝ) * (2 * Real.pi) := by
    rw [← hqcast]
    exact hxq
  have hleft :
      cfzp026ThirdQuadrantCellLeft k' τ + W.rectangle.T * ε ≤ x := by
    unfold cfzp026ThirdQuadrantCellLeft
    dsimp [x] at hxq'
    unfold cfzp028TargetLeft at hr
    nlinarith [hr.1]
  have hright :
      x + W.rectangle.T * ε ≤
        cfzp026ThirdQuadrantCellRight k' τ := by
    unfold cfzp026ThirdQuadrantCellRight
    dsimp [x] at hxq'
    unfold cfzp028TargetRight at hr
    nlinarith [hr.2]
  have hcenter_eq :
      W.rectangle.T * ((j : ℝ) * Real.log (p : ℝ)) = x := by
    dsimp [x, cfzp028PrimePhaseRotationStep]
    ring
  refine ⟨k', ?_⟩
  exact ⟨hcenter_eq ▸ hleft, hcenter_eq ▸ hright⟩

/-! ## Gate F/G: cofinal ready hits -/

/-- The positive rotation step makes the actual center tend to infinity. -/
theorem cfzp028_phaseCenter_tendsto_atTop
    (W : PascalCenteredXiResidueTransportWindow) {p : ℕ}
    (hstep : 0 < cfzp028PrimePhaseRotationStep W p) :
    Tendsto (fun j : ℕ =>
      (j : ℝ) * cfzp028PrimePhaseRotationStep W p) atTop atTop := by
  simpa [mul_comm] using
    (tendsto_natCast_atTop_atTop.const_mul_atTop hstep)

/-- Irrational rotation conditionally supplies CFZP-027's cofinal ready hits. -/
theorem cfzp028CofinalReadyThirdQuadrantHitsForPrime_of_irrationalRotation
    {ε τ : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    {p : ℕ} (hp : Nat.Prime p)
    (hε : 0 < ε) (hτ : 0 < τ) (hτ4 : τ ≤ Real.pi / 4)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (hinterior : Cfzp027ThirdQuadrantTargetHasInterior ε W τ)
    (hirr : Cfzp028PrimePhaseRotationIrrational W p) :
    Cfzp027CofinalReadyThirdQuadrantHitsForPrime ε W p τ := by
  letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  have hstep : 0 < cfzp028PrimePhaseRotationStep W p :=
    cfzp028PrimePhaseRotationStep_pos W hp
  have hdense := cfzp028_denseRange_nsmul_primePhaseRotation W hirr
  unfold Cfzp027CofinalReadyThirdQuadrantHitsForPrime
  intro J K
  obtain ⟨K₀, hready⟩ := cfzp027_exists_eventually_ready_cellIndex
    (cfzpModePhaseAspectRatio_pos W).le hsub
  let Ktot : ℕ := max K K₀
  have hcenter := cfzp028_phaseCenter_tendsto_atTop W hstep
  have hevent : ∀ᶠ j : ℕ in atTop,
      (2 * Real.pi * (Ktot : ℝ)) ≤
        (j : ℝ) * cfzp028PrimePhaseRotationStep W p := by
    exact hcenter.eventually (eventually_ge_atTop _)
  obtain ⟨J₀, hJ₀⟩ := (eventually_atTop.1 hevent)
  obtain ⟨j, hj, hjhit⟩ := cfzp028_exists_natMul_mem_open_ge hdense
    (cfzp028TargetCircle_isOpen W hε hτ hinterior)
    (cfzp028TargetCircle_nonempty W hinterior) (max J J₀)
  obtain ⟨k, hhit⟩ := cfzp028_quantitativeHit_of_targetCircle_mem W
    hε hτ hinterior hstep hjhit
  have hjlarge : J₀ ≤ j := le_trans (le_max_right _ _) hj
  have hkTot : Ktot ≤ k := by
    by_contra hK
    have hk' : k < Ktot := Nat.lt_of_not_ge hK
    rcases hhit with ⟨hleft, hright⟩
    unfold cfzp026ThirdQuadrantCellLeft at hleft
    have hkr : (k : ℝ) < (Ktot : ℝ) := by exact_mod_cast hk'
    have hP : 0 < 2 * Real.pi := by positivity
    have hcenter' := hJ₀ j hjlarge
    have hupper :
        W.rectangle.T * ((j : ℝ) * Real.log (p : ℝ)) <
          2 * Real.pi * ((k : ℝ) + 1) := by
      unfold cfzp026ThirdQuadrantCellRight at hright
      nlinarith [Real.pi_pos, mul_pos W.rectangle.hT hε, hτ]
    have hstep_eq :
        W.rectangle.T * ((j : ℝ) * Real.log (p : ℝ)) =
          (j : ℝ) * cfzp028PrimePhaseRotationStep W p := by
      unfold cfzp028PrimePhaseRotationStep
      ring
    have hnat : (k : ℝ) + 1 ≤ (Ktot : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hk')
    have hmul := mul_le_mul_of_nonneg_left hnat hP.le
    have hlow : 2 * Real.pi * (Ktot : ℝ) ≤
        W.rectangle.T * ((j : ℝ) * Real.log (p : ℝ)) :=
      hcenter'.trans_eq hstep_eq.symm
    exact (not_lt_of_ge hlow)
      (lt_of_lt_of_le hupper hmul)
  have hk : K ≤ k := le_trans (le_max_left _ _) hkTot
  have hkready : Cfzp027PhaseSinCoefficientReady
      (cfzpModePhaseAspectRatio W) k :=
    hready k (le_trans (le_max_right _ _) hkTot)
  exact ⟨j, k, le_trans (le_max_left _ _) hj, hk, hhit, hkready⟩

/-! ## Firewall -/

/-- The independent irrationality and window suppliers remain explicit gaps. -/
inductive Cfzp028AdditiveCircleIrrationalRotationCofinalHitGap : Prop
  | noIndependentPrimePhaseRotationIrrationalityProvider
  | noAutomaticSubcriticalWindowProvider
  | noCofinalCreditDebtDominanceProvider

end DkMath.RH.CFBRCProjection
