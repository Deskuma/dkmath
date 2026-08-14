/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideAggregateImbalanceMonotonicityAudit
import Mathlib.Tactic

/-!
# CS20: monotonicity strength and terminal-ceiling audit

This module classifies natural-cutoff monotonicity through adjacent finite
increments and records the weaker terminal-ceiling formulation obtained from
the already finite tail projection.  No prime-power mode sign, infinite
exchange, endpoint sign, fixed-defect RH argument, or RH conclusion is
asserted.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open MeasureTheory
open DkMath.NumberTheory.PrimitiveSet
open scoped Interval Topology

/-! ## CS20-A: exact adjacent cutoff increment -/

theorem pascalCenteredXiPrimeSideFinitePrimeBlockProjection_adjacent_eq_mode
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideFinitePrimeBlockProjection ε W X (X + 1) =
      (ArithmeticFunction.vonMangoldt (X + 1) : ℝ) *
        pascalCenteredXiPrimeSideFiniteModeKernel ε W (X + 1) := by
  have hblock := pascalCenteredXiPrimeSideFinitePrimeBlockProjection_eq_mode_sum_difference
    hε W X (X + 1)
  rw [hblock]
  simp only [Finset.sum_range_succ]
  ring

theorem pascalCenteredXiPrimeSideAggregateRayEnergyImbalance_adjacent_sub
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideAggregateRayEnergyImbalance ε W (X + 1) -
        pascalCenteredXiPrimeSideAggregateRayEnergyImbalance ε W X =
      4 * (ArithmeticFunction.vonMangoldt (X + 1) : ℝ) *
        pascalCenteredXiPrimeSideFiniteModeKernel ε W (X + 1) := by
  have hinc := pascalCenteredXiPrimeSideAggregateRayEnergyImbalance_sub
    hε W X (X + 1)
  calc
    pascalCenteredXiPrimeSideAggregateRayEnergyImbalance ε W (X + 1) -
          pascalCenteredXiPrimeSideAggregateRayEnergyImbalance ε W X =
        4 * pascalCenteredXiPrimeSideFinitePrimeBlockProjection ε W X (X + 1) := hinc
    _ = 4 * (ArithmeticFunction.vonMangoldt (X + 1) : ℝ) *
          pascalCenteredXiPrimeSideFiniteModeKernel ε W (X + 1) := by
      rw [pascalCenteredXiPrimeSideFinitePrimeBlockProjection_adjacent_eq_mode hε W X]
      ring

/-! ## CS20-B: monotonicity versus adjacent increments -/

theorem monotone_iff_adjacent_sub_nonneg
    (f : ℕ → ℝ) :
    Monotone f ↔ ∀ X : ℕ, 0 ≤ f (X + 1) - f X := by
  constructor
  · intro hf X
    have h := hf (Nat.le_succ X)
    nlinarith
  · intro h X Y hXY
    exact (monotone_nat_of_le_succ (fun n => by
      have hn := h n
      nlinarith)) hXY

theorem pascalCenteredXiPrimeSideAggregateRayEnergyImbalance_monotone_iff_adjacent_mode_nonneg
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    Monotone (pascalCenteredXiPrimeSideAggregateRayEnergyImbalance ε W) ↔
      ∀ X : ℕ,
        0 ≤ (ArithmeticFunction.vonMangoldt (X + 1) : ℝ) *
          pascalCenteredXiPrimeSideFiniteModeKernel ε W (X + 1) := by
  rw [monotone_iff_adjacent_sub_nonneg]
  constructor
  · intro h X
    have hX := h X
    have hadj := pascalCenteredXiPrimeSideAggregateRayEnergyImbalance_adjacent_sub
      hε W X
    nlinarith
  · intro h X
    have hX := h X
    have hadj := pascalCenteredXiPrimeSideAggregateRayEnergyImbalance_adjacent_sub
      hε W X
    nlinarith

/-! ## CS20-C: prime-power local strength -/

theorem pascalCenteredXiPrimeSideFiniteModeCoefficient_mul_nonneg_iff_primePowerKernel_nonneg
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j)
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) :
    0 ≤ (ArithmeticFunction.vonMangoldt (p ^ j) : ℝ) *
        pascalCenteredXiPrimeSideFiniteModeKernel ε W (p ^ j) ↔
    0 ≤ pascalCenteredXiPrimeSideFiniteModeKernel ε W (p ^ j) := by
  have hcost : (ArithmeticFunction.vonMangoldt (p ^ j) : ℝ) =
      Real.log (p : ℝ) := by
    rw [ArithmeticFunction.vonMangoldt_apply_pow (Nat.ne_of_gt hj),
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hlog : 0 < Real.log (p : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hp.one_lt
  rw [hcost]
  constructor <;> intro h
  · nlinarith
  · exact mul_nonneg hlog.le h

theorem pascalCenteredXiPrimeSideFiniteModeCoefficient_mul_eq_zero_of_not_primePower
    {q : ℕ} (hq : ¬ IsPrimePow q)
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) :
    (ArithmeticFunction.vonMangoldt q : ℝ) *
        pascalCenteredXiPrimeSideFiniteModeKernel ε W q = 0 := by
  rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hq]
  simp

theorem pascalCenteredXiPrimeSideAggregateRayEnergyImbalance_monotone_iff_primePower_mode_nonneg
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    Monotone (pascalCenteredXiPrimeSideAggregateRayEnergyImbalance ε W) ↔
      ∀ p j : ℕ, Nat.Prime p → 0 < j →
        0 ≤ pascalCenteredXiPrimeSideFiniteModeKernel ε W (p ^ j) := by
  rw [pascalCenteredXiPrimeSideAggregateRayEnergyImbalance_monotone_iff_adjacent_mode_nonneg
    hε W]
  constructor
  · intro h p j hp hj
    have hq := h (p ^ j - 1)
    have hsucc : p ^ j - 1 + 1 = p ^ j := by
      apply Nat.sub_add_cancel
      have hpj : 0 < p ^ j := pow_pos hp.pos j
      omega
    rw [hsucc] at hq
    exact (pascalCenteredXiPrimeSideFiniteModeCoefficient_mul_nonneg_iff_primePowerKernel_nonneg
      hp hj ε W).mp hq
  · intro h X
    by_cases hq : IsPrimePow (X + 1)
    · rcases (isPrimePow_nat_iff (X + 1)).mp hq with ⟨p, j, hp, hj, hpj⟩
      have hmode := h p j hp hj
      have hcoeff :=
        (pascalCenteredXiPrimeSideFiniteModeCoefficient_mul_nonneg_iff_primePowerKernel_nonneg
          hp hj ε W).mpr hmode
      simpa [hpj] using hcoeff
    · rw [pascalCenteredXiPrimeSideFiniteModeCoefficient_mul_eq_zero_of_not_primePower
        hq ε W]

/-! ## CS20-D: the classification is a strength result, not a sign provider -/

inductive PascalCenteredXiPrimeSideAdjacentPrimePowerModeSignGap : Prop
  | noIndependentPositivePrimePowerModeKernelProvider

/-! ## CS20-E: terminal imbalance without monotonicity -/

noncomputable def pascalCenteredXiPrimeSideAggregateRayEnergyTerminal
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  4 * pascalCenteredXiPrimeSideFiniteTailProjection ε W 0

theorem pascalCenteredXiPrimeSideAggregateRayEnergyImbalance_tendsto_terminal
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    Tendsto
      (pascalCenteredXiPrimeSideAggregateRayEnergyImbalance ε W)
      atTop
      (nhds (pascalCenteredXiPrimeSideAggregateRayEnergyTerminal ε W)) := by
  have hconv := pascalCenteredXiPrimeSideFiniteTailProjection_tendsto_zero hε W
  have hzero := pascalCenteredXiPrimeSideAggregateRayEnergyImbalance_zero hε W
  have hEq : ∀ Y : ℕ,
      pascalCenteredXiPrimeSideAggregateRayEnergyImbalance ε W Y =
        pascalCenteredXiPrimeSideAggregateRayEnergyTerminal ε W -
          4 * pascalCenteredXiPrimeSideFiniteTailProjection ε W Y := by
    intro Y
    have htail := pascalCenteredXiPrimeSideFiniteTailProjection_sub_eq_imbalance_increment
      hε W 0 Y
    dsimp [pascalCenteredXiPrimeSideAggregateRayEnergyTerminal]
    rw [hzero] at htail
    nlinarith
  rw [funext hEq]
  have hscaled : Tendsto
    (fun Y : ℕ => (4 : ℝ) * pascalCenteredXiPrimeSideFiniteTailProjection ε W Y)
      atTop (nhds 0) :=
    by simpa using
      ((tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (4 : ℝ)) atTop (nhds 4)).mul hconv)
  simpa using (tendsto_const_nhds.sub hscaled)

/-! ## CS20-F: exact terminal ceiling -/

theorem pascalCenteredXiPrimeSideFiniteTailProjection_terminal_ceiling
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    4 * pascalCenteredXiPrimeSideFiniteTailProjection ε W X =
      pascalCenteredXiPrimeSideAggregateRayEnergyTerminal ε W -
        pascalCenteredXiPrimeSideAggregateRayEnergyImbalance ε W X := by
  have hconv := pascalCenteredXiPrimeSideFiniteTailProjection_tendsto_zero hε W
  have hterm := pascalCenteredXiPrimeSideAggregateRayEnergyImbalance_tendsto_terminal hε W
  have hEq : ∀ Y : ℕ,
      pascalCenteredXiPrimeSideAggregateRayEnergyImbalance ε W Y -
          pascalCenteredXiPrimeSideAggregateRayEnergyImbalance ε W X +
          4 * pascalCenteredXiPrimeSideFiniteTailProjection ε W Y =
        4 * pascalCenteredXiPrimeSideFiniteTailProjection ε W X := by
    intro Y
    have htail := pascalCenteredXiPrimeSideFiniteTailProjection_sub_eq_imbalance_increment
      hε W X Y
    nlinarith
  have hleft : Tendsto
      (fun Y : ℕ =>
        pascalCenteredXiPrimeSideAggregateRayEnergyImbalance ε W Y -
          pascalCenteredXiPrimeSideAggregateRayEnergyImbalance ε W X +
          4 * pascalCenteredXiPrimeSideFiniteTailProjection ε W Y)
      atTop
      (nhds (pascalCenteredXiPrimeSideAggregateRayEnergyTerminal ε W -
        pascalCenteredXiPrimeSideAggregateRayEnergyImbalance ε W X)) := by
    have hscaled : Tendsto
        (fun Y : ℕ => (4 : ℝ) * pascalCenteredXiPrimeSideFiniteTailProjection ε W Y)
        atTop (nhds 0) :=
      by simpa using
        ((tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (4 : ℝ)) atTop (nhds 4)).mul hconv)
    simpa using (hterm.sub tendsto_const_nhds).add hscaled
  have hleft' : Tendsto
      (fun _ : ℕ => 4 * pascalCenteredXiPrimeSideFiniteTailProjection ε W X)
      atTop
      (nhds (pascalCenteredXiPrimeSideAggregateRayEnergyTerminal ε W -
        pascalCenteredXiPrimeSideAggregateRayEnergyImbalance ε W X)) := by
    rw [← funext hEq]
    exact hleft
  have hright : Tendsto
      (fun _ : ℕ => 4 * pascalCenteredXiPrimeSideFiniteTailProjection ε W X)
      atTop (nhds (4 * pascalCenteredXiPrimeSideFiniteTailProjection ε W X)) :=
    tendsto_const_nhds
  have huniq := tendsto_nhds_unique hleft' hright
  exact huniq.symm

theorem pascalCenteredXiPrimeSideFiniteTailProjection_nonneg_iff_terminal_ceiling
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    0 ≤ pascalCenteredXiPrimeSideFiniteTailProjection ε W X ↔
      pascalCenteredXiPrimeSideAggregateRayEnergyImbalance ε W X ≤
        pascalCenteredXiPrimeSideAggregateRayEnergyTerminal ε W := by
  have hceiling := pascalCenteredXiPrimeSideFiniteTailProjection_terminal_ceiling hε W X
  constructor <;> intro h <;> nlinarith [hceiling]

theorem pascalCenteredXiPrimeSideFiniteTailProjection_nonpos_iff_terminal_floor
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideFiniteTailProjection ε W X ≤ 0 ↔
      pascalCenteredXiPrimeSideAggregateRayEnergyTerminal ε W ≤
        pascalCenteredXiPrimeSideAggregateRayEnergyImbalance ε W X := by
  have hceiling := pascalCenteredXiPrimeSideFiniteTailProjection_terminal_ceiling hε W X
  constructor <;> intro h <;> nlinarith [hceiling]

/-! ## CS20-G: monotonicity is sufficient, not necessary -/

theorem pascalCenteredXiPrimeSideAggregateRayEnergyImbalance_monotone_implies_terminal_ceiling
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (hmono : Monotone (pascalCenteredXiPrimeSideAggregateRayEnergyImbalance ε W)) :
    ∀ X : ℕ,
      pascalCenteredXiPrimeSideAggregateRayEnergyImbalance ε W X ≤
        pascalCenteredXiPrimeSideAggregateRayEnergyTerminal ε W := by
  intro X
  apply (pascalCenteredXiPrimeSideFiniteTailProjection_nonneg_iff_terminal_ceiling
    hε W X).mp
  exact pascalCenteredXiPrimeSideFiniteTailProjection_nonneg_of_monotone_imbalance_fixed_epsilon
    hε W hmono X

/-! ## CS20-H: source frontier -/

inductive PascalCenteredXiPrimeSideAggregateTerminalCeilingGap : Prop
  | noIndependentAggregateTerminalCeilingProvider

end DkMath.RH.CFBRCProjection
