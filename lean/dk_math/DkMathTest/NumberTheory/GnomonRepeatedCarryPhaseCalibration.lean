/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.GnomonRepeatedCarryPhase
import DkMathTest.NumberTheory.GnomonCarryFiberCalibration

#print "file: DkMathTest.NumberTheory.GnomonRepeatedCarryPhaseCalibration"

namespace DkMathTest.NumberTheory.GnomonRepeatedCarryPhaseCalibration
open DkMath.NumberTheory.Legendre
open scoped BigOperators

/-- A retained higher power need not carry: the envelope discards phase information. -/
theorem proper_overcover69_checked :
    512 ∈ gnomonRepeatedPhaseEnvelope 69 ∧ gnomonLowDivisorCarryBit 69 512 = 0 := by
  simp only [gnomonRepeatedPhaseEnvelope, Finset.mem_filter, Finset.mem_Icc]
  decide +kernel

/-- Base 5 fails at its first eligible power and its whole later chain is excluded. -/
theorem excluded625_checked :
    625 ∈ (Finset.Icc (2 * 69 + 1) (69 ^ 2)).filter (fun d => ¬ d.Prime) ∧
    625 ∉ gnomonRepeatedPhaseEnvelope 69 ∧ ¬ gnomonRepeatedBaseActive 69 5 := by
  simp only [gnomonRepeatedPhaseEnvelope, Finset.mem_filter, Finset.mem_Icc]
  decide +kernel

theorem strict_saving69 : gnomonRepeatedPhaseBudget 69 < gnomonRepeatedCarryBandBudget 69 := by
  have h := gnomonRepeatedPhaseBudget_add_excluded_le_band
    excluded625_checked.1 excluded625_checked.2.1
  have hw : ArithmeticFunction.vonMangoldt 625 = Real.log (5 : ℝ) := by
    exact gnomonCarry_prime_pow_weight (by norm_num : Nat.Prime 5) (by norm_num : 0 < 4)
  rw [hw] at h
  have hp : 0 < Real.log (5 : ℝ) := Real.log_pos (by norm_num)
  linarith

theorem base2_2896_checked :
    gnomonRepeatedFirstExponent 2896 2 = 13 ∧ gnomonRepeatedBaseActive 2896 2 ∧
    Nat.log 2 (2896 ^ 2) = 22 := by
  decide +kernel

theorem fiber2896_retained :
    gnomonLargeCarryExponents 2896 2 8388608 = Finset.Icc 13 22 ∧
    (gnomonLargeCarryExponents 2896 2 8388608).card = 10 :=
  ⟨GnomonCarryFiberCalibration.fiber2896_checked,
    GnomonCarryFiberCalibration.fiber2896_card_checked⟩

theorem interval2896_weight :
    (∑ a ∈ Finset.Icc (gnomonRepeatedFirstExponent 2896 2) (Nat.log 2 (2896 ^ 2)),
      ArithmeticFunction.vonMangoldt (2 ^ a)) = 10 * Real.log (2 : ℝ) := by
  rw [gnomonRepeatedExponentInterval_weight 2896 (by norm_num),
    base2_2896_checked.1, base2_2896_checked.2.2]
  norm_num

/-- Every one of the ten labels passes the envelope; no target quotienting occurs. -/
theorem all_ten_labels_retained : ∀ a ∈ Finset.Icc 13 22,
    2 ^ a ∈ gnomonRepeatedPhaseEnvelope 2896 := by
  intro a ha
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp ha
  have hlow := Nat.pow_le_pow_right (by norm_num : 0 < 2) hlo
  have hhigh := Nat.pow_le_pow_right (by norm_num : 0 < 2) hhi
  have hm : (2 ^ a).minFac = 2 :=
    (by norm_num : Nat.Prime 2).pow_minFac (by omega)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩,
    Nat.Prime.not_prime_pow (by omega : 2 ≤ a)⟩, ?_⟩
  · norm_num at hlow ⊢
    omega
  · norm_num at hhigh ⊢
    omega
  · rw [hm]
    exact base2_2896_checked.2.1

/-- Fixed scalar phase anchors avoid scanning a quadratic carrier in regression proofs. -/
theorem retained_anchor_gates :
    gnomonRepeatedBaseActive 32 3 ∧ gnomonRepeatedBaseActive 69 2 ∧
    gnomonRepeatedBaseActive 297 5 ∧ gnomonRepeatedBaseActive 1031 2 ∧
    gnomonRepeatedBaseActive 5000 2 ∧ ¬ gnomonRepeatedBaseActive 3 2 ∧
    ¬ gnomonRepeatedBaseActive 3 3 := by
  decide +kernel

end DkMathTest.NumberTheory.GnomonRepeatedCarryPhaseCalibration
