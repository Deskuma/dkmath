/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaInteractionCutoffDynamicsAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaInteractionPrimePowerEventAudit"

/-!
# CFZP-006S: von Mangoldt prime-power event classification

The cutoff increment is supported on the intersection of the classical
prime-power support and the nonzero finite-mode-kernel support.  Consequently
non-prime-power indices give exact no-update steps, while a witnessed
prime-power step has the explicit weight `2 * log p * K`.  No sign assertion
for `K`, monotonicity, reach, or RH conclusion is supplied here.
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

/-! ## A. Prime-power support and exact event classification -/

theorem cfzpPrimeSideInteractionCutoffIncrement_ne_zero_implies_isPrimePow
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (n : ℕ)
    (hinc : cfzpPrimeSideInteractionCutoffIncrement ε W n ≠ 0) :
    IsPrimePow n := by
  exact ArithmeticFunction.vonMangoldt_ne_zero_iff.mp
    (cfzpPrimeSideInteractionCutoffIncrement_ne_zero_implies_vonMangoldt_ne_zero
      ε W n hinc)

theorem cfzpPrimeSideInteractionCutoffIncrement_ne_zero_iff_isPrimePow_and_modeKernel_ne_zero
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (n : ℕ) :
    cfzpPrimeSideInteractionCutoffIncrement ε W n ≠ 0 ↔
      IsPrimePow n ∧ pascalCenteredXiPrimeSideFiniteModeKernel ε W n ≠ 0 := by
  constructor
  · intro hinc
    exact ⟨cfzpPrimeSideInteractionCutoffIncrement_ne_zero_implies_isPrimePow
      ε W n hinc,
      cfzpPrimeSideInteractionCutoffIncrement_ne_zero_implies_modeKernel_ne_zero
        ε W n hinc⟩
  · rintro ⟨hprimepow, hkernel⟩
    have hΛ : (ArithmeticFunction.vonMangoldt n : ℝ) ≠ 0 :=
      ArithmeticFunction.vonMangoldt_ne_zero_iff.mpr hprimepow
    unfold cfzpPrimeSideInteractionCutoffIncrement
    exact mul_ne_zero (mul_ne_zero (by norm_num) hΛ) hkernel

/-! ## B. The non-prime-power no-update family -/

theorem cfzpAggregateRayInteractionEnergy_succ_eq_of_not_isPrimePow
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (hNP : ¬ IsPrimePow (X + 1)) :
    pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W (X + 1) =
      pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X := by
  apply cfzpAggregateRayInteractionEnergy_succ_eq_of_vonMangoldt_eq_zero hε W X
  exact ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hNP

theorem cfzpRadialBudgetResidual_succ_eq_of_not_isPrimePow
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (hNP : ¬ IsPrimePow (X + 1)) :
    cfzpRadialBudgetResidual ε W (X + 1) =
      cfzpRadialBudgetResidual ε W X := by
  apply cfzpRadialBudgetResidual_succ_eq_of_vonMangoldt_eq_zero hε W X
  exact ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hNP

theorem cfzpRadialContactDeficit_succ_eq_of_not_isPrimePow
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (hNP : ¬ IsPrimePow (X + 1)) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W (X + 1) =
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X := by
  apply cfzpRadialContactDeficit_succ_eq_of_vonMangoldt_eq_zero hε W X
  exact ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hNP

/-! ## C. A witnessed prime power and its explicit logarithmic weight -/

theorem cfzpPrimeSideInteractionCutoffIncrement_eq_two_log_mul_modeKernel_of_eq_prime_pow
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    {p k n : ℕ} (hp : Nat.Prime p) (hk : 0 < k) (hn : n = p ^ k) :
    cfzpPrimeSideInteractionCutoffIncrement ε W n =
      2 * Real.log (p : ℝ) * pascalCenteredXiPrimeSideFiniteModeKernel ε W n := by
  rw [hn]
  unfold cfzpPrimeSideInteractionCutoffIncrement
  rw [ArithmeticFunction.vonMangoldt_apply_pow (Nat.ne_of_gt hk),
    ArithmeticFunction.vonMangoldt_apply_prime hp]

/-! ## D. Explicit successor updates at witnessed prime-power events -/

theorem cfzpAggregateRayInteractionEnergy_succ_eq_of_eq_prime_pow
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    {p k : ℕ} (hp : Nat.Prime p) (hk : 0 < k)
    (hstep : X + 1 = p ^ k) :
    pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W (X + 1) =
      pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X +
        2 * Real.log (p : ℝ) *
          pascalCenteredXiPrimeSideFiniteModeKernel ε W (X + 1) := by
  have h := cfzpAggregateRayInteractionEnergy_succ hε W X
  have hinc :=
    cfzpPrimeSideInteractionCutoffIncrement_eq_two_log_mul_modeKernel_of_eq_prime_pow
      ε W hp hk hstep
  rw [hinc] at h
  exact h

theorem cfzpRadialBudgetResidual_succ_eq_of_eq_prime_pow
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    {p k : ℕ} (hp : Nat.Prime p) (hk : 0 < k)
    (hstep : X + 1 = p ^ k) :
    cfzpRadialBudgetResidual ε W (X + 1) =
      cfzpRadialBudgetResidual ε W X -
        2 * Real.log (p : ℝ) *
          pascalCenteredXiPrimeSideFiniteModeKernel ε W (X + 1) := by
  have h := cfzpRadialBudgetResidual_succ hε W X
  have hinc :=
    cfzpPrimeSideInteractionCutoffIncrement_eq_two_log_mul_modeKernel_of_eq_prime_pow
      ε W hp hk hstep
  rw [hinc] at h
  exact h

theorem cfzpRadialContactDeficit_succ_eq_of_eq_prime_pow
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    {p k : ℕ} (hp : Nat.Prime p) (hk : 0 < k)
    (hstep : X + 1 = p ^ k) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W (X + 1) =
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X -
        2 * Real.log (p : ℝ) *
          pascalCenteredXiPrimeSideFiniteModeKernel ε W (X + 1) := by
  have h := cfzpRadialContactDeficit_succ hε W X
  have hinc :=
    cfzpPrimeSideInteractionCutoffIncrement_eq_two_log_mul_modeKernel_of_eq_prime_pow
      ε W hp hk hstep
  rw [hinc] at h
  exact h

inductive CfzpPrimePowerModeKernelSignGap : Prop
  | noIndependentPrimePowerModeKernelSignProvider

end DkMath.RH.CFBRCProjection
