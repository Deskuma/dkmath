/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideCF2DPolarizationBridgeAudit
import Mathlib.Tactic

/-!
# CS19: finite aggregate imbalance and cutoff monotonicity audit

This module packages the finite cutoff dynamics exposed by CS12, CS17, and
CS18.  It proves exact increment and tail-projection adapters, transports an
already-authorized fixed-ε residual limit when supplied, and isolates cutoff
monotonicity as the remaining provider gap.  No infinite exchange, endpoint
sign theorem, fixed-defect RH argument, or RH conclusion is asserted.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open MeasureTheory
open scoped Interval Topology

/-! ## CS19-A: named aggregate imbalance -/

noncomputable def pascalCenteredXiPrimeSideAggregateRayEnergyImbalance
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) : ℝ :=
  pascalCenteredXiPrimeSideAggregateRayPlusEnergy ε W X -
    pascalCenteredXiPrimeSideAggregateRayMinusEnergy ε W X

theorem pascalCenteredXiPrimeSideAggregateRayEnergyImbalance_eq_four_mul_modeSum
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideAggregateRayEnergyImbalance ε W X =
      4 * (∑ n ∈ Finset.range (X + 1),
        (ArithmeticFunction.vonMangoldt n : ℝ) *
          pascalCenteredXiPrimeSideFiniteModeKernel ε W n) := by
  unfold pascalCenteredXiPrimeSideAggregateRayEnergyImbalance
  exact (pascalCenteredXiPrimeSideFiniteModeSum_eq_aggregateRayEnergy_difference
    hε W X).symm

theorem pascalCenteredXiPrimeSideAggregateRayEnergyImbalance_order_iff_modeSum_nonneg
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    0 ≤ pascalCenteredXiPrimeSideAggregateRayEnergyImbalance ε W X ↔
      0 ≤ (∑ n ∈ Finset.range (X + 1),
        (ArithmeticFunction.vonMangoldt n : ℝ) *
          pascalCenteredXiPrimeSideFiniteModeKernel ε W n) := by
  rw [pascalCenteredXiPrimeSideAggregateRayEnergyImbalance_eq_four_mul_modeSum hε W X]
  constructor <;> intro h <;> nlinarith

theorem pascalCenteredXiPrimeSideAggregateRayEnergyImbalance_zero
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    pascalCenteredXiPrimeSideAggregateRayEnergyImbalance ε W 0 = 0 := by
  rw [pascalCenteredXiPrimeSideAggregateRayEnergyImbalance_eq_four_mul_modeSum hε W 0]
  simp

/-! ## CS19-B: exact cutoff increment / block identity -/

theorem pascalCenteredXiPrimeSideAggregateRayEnergyImbalance_sub
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X Y : ℕ) :
    pascalCenteredXiPrimeSideAggregateRayEnergyImbalance ε W Y -
        pascalCenteredXiPrimeSideAggregateRayEnergyImbalance ε W X =
      4 * pascalCenteredXiPrimeSideFinitePrimeBlockProjection ε W X Y := by
  have hY := pascalCenteredXiPrimeSideAggregateRayEnergyImbalance_eq_four_mul_modeSum
    hε W Y
  have hX := pascalCenteredXiPrimeSideAggregateRayEnergyImbalance_eq_four_mul_modeSum
    hε W X
  have hblock := pascalCenteredXiPrimeSideFinitePrimeBlockProjection_eq_mode_sum_difference
    hε W X Y
  nlinarith [hY, hX, hblock]

theorem pascalCenteredXiPrimeSideAggregateRayEnergyImbalance_order_iff_blockProjection_nonneg
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X Y : ℕ) :
    pascalCenteredXiPrimeSideAggregateRayEnergyImbalance ε W X ≤
        pascalCenteredXiPrimeSideAggregateRayEnergyImbalance ε W Y ↔
      0 ≤ pascalCenteredXiPrimeSideFinitePrimeBlockProjection ε W X Y := by
  have hinc := pascalCenteredXiPrimeSideAggregateRayEnergyImbalance_sub hε W X Y
  constructor <;> intro h <;> nlinarith [hinc]

/-! ## CS19-C: tail projection / imbalance difference -/

theorem pascalCenteredXiPrimeSideFiniteTailProjection_sub_eq_imbalance_increment
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X Y : ℕ) :
    4 * (pascalCenteredXiPrimeSideFiniteTailProjection ε W X -
        pascalCenteredXiPrimeSideFiniteTailProjection ε W Y) =
      pascalCenteredXiPrimeSideAggregateRayEnergyImbalance ε W Y -
        pascalCenteredXiPrimeSideAggregateRayEnergyImbalance ε W X := by
  have htail := pascalCenteredXiPrimeSideFiniteTailProjection_sub_eq_blockProjection
    ε W X Y
  have hinc := pascalCenteredXiPrimeSideAggregateRayEnergyImbalance_sub hε W X Y
  nlinarith [htail, hinc]

theorem pascalCenteredXiPrimeSideAggregateRayEnergyImbalance_order_iff_tailProjection_order
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X Y : ℕ) :
    pascalCenteredXiPrimeSideAggregateRayEnergyImbalance ε W X ≤
        pascalCenteredXiPrimeSideAggregateRayEnergyImbalance ε W Y ↔
      pascalCenteredXiPrimeSideFiniteTailProjection ε W Y ≤
        pascalCenteredXiPrimeSideFiniteTailProjection ε W X := by
  have hEq := pascalCenteredXiPrimeSideFiniteTailProjection_sub_eq_imbalance_increment
    hε W X Y
  constructor <;> intro h <;> nlinarith [hEq]

/-! ## CS19-D: fixed-ε convergence transport -/

theorem pascalCenteredXiPrimeSideFiniteTailProjection_tendsto_zero_of_approximant
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (happrox : Tendsto
      (fun X : ℕ => pascalCenteredXiMellinQuadraticArithmeticDefectApproximant
        ε W X)
      atTop
      (nhds (pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint ε W))) :
    Tendsto
      (fun X : ℕ => pascalCenteredXiPrimeSideFiniteTailProjection ε W X)
      atTop (nhds 0) := by
  have hEq : ∀ X : ℕ,
      pascalCenteredXiMellinQuadraticArithmeticDefectApproximant ε W X -
          pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint ε W =
        (2 / Real.pi) *
          pascalCenteredXiPrimeSideFiniteTailProjection ε W X := by
    intro X
    exact pascalCenteredXiMellinQuadraticArithmeticDefectApproximant_sub_endpoint_eq_tailProjection
      hε W X
  have hleft : Tendsto
      (fun X : ℕ =>
        pascalCenteredXiMellinQuadraticArithmeticDefectApproximant ε W X -
          pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint ε W)
      atTop (nhds 0) := by
    convert happrox.sub tendsto_const_nhds using 1
    simp
  have hscaled : Tendsto
      (fun X : ℕ =>
        (2 / Real.pi : ℝ) *
          pascalCenteredXiPrimeSideFiniteTailProjection ε W X)
      atTop (nhds 0) := by
    rw [← funext hEq]
    exact hleft
  have hrecover : Tendsto
      (fun X : ℕ =>
        (Real.pi / 2 : ℝ) *
          ((2 / Real.pi : ℝ) *
            pascalCenteredXiPrimeSideFiniteTailProjection ε W X))
      atTop (nhds ((Real.pi / 2 : ℝ) * 0)) := by
    exact (tendsto_const_nhds.mul hscaled)
  convert hrecover using 1
  · funext X
    field_simp [Real.pi_ne_zero]
  · simp

theorem pascalCenteredXiPrimeSideFiniteTailProjection_tendsto_zero
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    Tendsto
      (fun X : ℕ => pascalCenteredXiPrimeSideFiniteTailProjection ε W X)
      atTop (nhds 0) := by
  exact pascalCenteredXiPrimeSideFiniteTailProjection_tendsto_zero_of_approximant
    hε W (tendsto_pascalCenteredXiMellinQuadraticArithmeticDefectApproximant hε W)

/-! ## CS19-E: monotonicity is an adapter, not a provider -/

theorem pascalCenteredXiPrimeSideFiniteTailProjection_nonneg_of_monotone_imbalance
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (hmono : Monotone (pascalCenteredXiPrimeSideAggregateRayEnergyImbalance ε W))
    (hconv : Tendsto
      (fun X : ℕ => pascalCenteredXiPrimeSideFiniteTailProjection ε W X)
      atTop (nhds 0)) :
    ∀ X : ℕ, 0 ≤ pascalCenteredXiPrimeSideFiniteTailProjection ε W X := by
  intro X
  by_contra hnot
  have hneg : pascalCenteredXiPrimeSideFiniteTailProjection ε W X < 0 :=
    lt_of_not_ge hnot
  have hev : ∀ᶠ Y : ℕ in atTop,
      pascalCenteredXiPrimeSideFiniteTailProjection ε W X <
        pascalCenteredXiPrimeSideFiniteTailProjection ε W Y :=
    hconv (Ioi_mem_nhds hneg)
  rcases (eventually_atTop.1 hev) with ⟨N, hN⟩
  let Y : ℕ := max X N
  have hXY : X ≤ Y := le_max_left _ _
  have hNY : N ≤ Y := le_max_right _ _
  have htail : pascalCenteredXiPrimeSideFiniteTailProjection ε W Y ≤
      pascalCenteredXiPrimeSideFiniteTailProjection ε W X := by
    have himbalance := hmono hXY
    exact (pascalCenteredXiPrimeSideAggregateRayEnergyImbalance_order_iff_tailProjection_order
      hε W X Y).mp himbalance
  have hgt := hN Y hNY
  linarith

theorem pascalCenteredXiPrimeSideFiniteTailProjection_nonneg_of_monotone_imbalance_fixed_epsilon
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (hmono : Monotone (pascalCenteredXiPrimeSideAggregateRayEnergyImbalance ε W)) :
    ∀ X : ℕ, 0 ≤ pascalCenteredXiPrimeSideFiniteTailProjection ε W X :=
  pascalCenteredXiPrimeSideFiniteTailProjection_nonneg_of_monotone_imbalance
    hε W hmono (pascalCenteredXiPrimeSideFiniteTailProjection_tendsto_zero hε W)

/-! ## CS19-F: absolute ordering versus cutoff monotonicity -/

theorem pascalCenteredXiPrimeSideAggregateRayEnergyImbalance_nonneg_of_zero_base_monotone
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    (hbase : pascalCenteredXiPrimeSideAggregateRayEnergyImbalance ε W 0 = 0)
    (hmono : Monotone (pascalCenteredXiPrimeSideAggregateRayEnergyImbalance ε W)) :
    ∀ X : ℕ, 0 ≤ pascalCenteredXiPrimeSideAggregateRayEnergyImbalance ε W X := by
  intro X
  have h := hmono (Nat.zero_le X)
  rw [hbase] at h
  exact h

/-! ## CS19-G: source audit frontier -/

/- The finite identities above reduce a tail sign to cutoff monotonicity.  The
prime-side source supplies no independent positivity theorem for every
incremental block, so monotonicity remains an explicit provider gap. -/
inductive PascalCenteredXiPrimeSideAggregateImbalanceMonotonicityGap : Prop
  | noIndependentCutoffMonotonicityProvider

end DkMath.RH.CFBRCProjection
