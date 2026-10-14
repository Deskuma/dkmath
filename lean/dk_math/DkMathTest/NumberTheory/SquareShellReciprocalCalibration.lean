/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.NumberTheory.SquareShellPrimePowerCalibration

#print "file: DkMathTest.NumberTheory.SquareShellReciprocalCalibration"

namespace DkMathTest.NumberTheory.SquareShellReciprocalCalibration

open DkMath.NumberTheory DkMath.NumberTheory.Legendre

/-- A symbolic event certificate keeps all finite membership and exact weight data. -/
theorem event_depth_packet {n q a : ℕ} (hq : q ∈ shellHigherPrimePowerEvents n)
    (ha : q.factorization q.minFac = a) :
    q ∈ shellHigherPrimePowerEvents n ∧ q.factorization q.minFac = a ∧
    a ∈ shellHigherPrimePowerDepths n ∧ a ∈ shellOddDepths n ∧
    ArithmeticFunction.vonMangoldt q = Real.log (q : ℝ) / (a : ℝ) := by
  have hd := mem_shellHigherPrimePowerDepths.mpr ⟨q, hq, ha.symm⟩
  refine ⟨hq, ha, hd, shellHigherPrimePowerDepths_subset_oddDepths n hd, ?_⟩
  rw [shellHigherPrimePower_weight_eq_log_div_depth hq, ha]

/-- Factorization depth is certified through prime powers, avoiding giant trial division. -/
theorem prime_power_canonical_depth {p a : ℕ} (hp : p.Prime) (ha : a ≠ 0) :
    (p ^ a).factorization (p ^ a).minFac = a := by
  rw [hp.pow_minFac ha, Nat.factorization_pow_self hp]

/-- Canonical depth, both carriers and exact symbolic log/depth weight. -/
theorem event8_packet_checked :
    8 ∈ shellHigherPrimePowerEvents 2 ∧
    (8 : ℕ).factorization (8 : ℕ).minFac = 3 ∧
    3 ∈ shellHigherPrimePowerDepths 2 ∧ 3 ∈ shellOddDepths 2 ∧
    ArithmeticFunction.vonMangoldt 8 = Real.log (8 : ℝ) / 3 := by
  apply event_depth_packet
  · apply mem_shellHigherPrimePowerEvents.mpr
    refine ⟨by norm_num [SquareCell], ?_, by norm_num⟩
    exact (isPrimePow_nat_iff 8).mpr ⟨2, 3, by norm_num, by omega, by norm_num⟩
  · change (2 ^ 3).factorization (2 ^ 3).minFac = 3
    exact prime_power_canonical_depth (by norm_num) (by omega)

/-- Canonical depth, both carriers and exact symbolic log/depth weight. -/
theorem event27_packet_checked :
    27 ∈ shellHigherPrimePowerEvents 5 ∧
    (27 : ℕ).factorization (27 : ℕ).minFac = 3 ∧
    3 ∈ shellHigherPrimePowerDepths 5 ∧ 3 ∈ shellOddDepths 5 ∧
    ArithmeticFunction.vonMangoldt 27 = Real.log (27 : ℝ) / 3 := by
  apply event_depth_packet
  · apply mem_shellHigherPrimePowerEvents.mpr
    refine ⟨by norm_num [SquareCell], ?_, by norm_num⟩
    exact (isPrimePow_nat_iff 27).mpr ⟨3, 3, by norm_num, by omega, by norm_num⟩
  · change (3 ^ 3).factorization (3 ^ 3).minFac = 3
    exact prime_power_canonical_depth (by norm_num) (by omega)

/-- Canonical depth, both carriers and exact symbolic log/depth weight. -/
theorem event32_packet_checked :
    32 ∈ shellHigherPrimePowerEvents 5 ∧
    (32 : ℕ).factorization (32 : ℕ).minFac = 5 ∧
    5 ∈ shellHigherPrimePowerDepths 5 ∧ 5 ∈ shellOddDepths 5 ∧
    ArithmeticFunction.vonMangoldt 32 = Real.log (32 : ℝ) / 5 := by
  apply event_depth_packet
  · apply mem_shellHigherPrimePowerEvents.mpr
    refine ⟨by norm_num [SquareCell], ?_, by norm_num⟩
    exact (isPrimePow_nat_iff 32).mpr ⟨2, 5, by norm_num, by omega, by norm_num⟩
  · change (2 ^ 5).factorization (2 ^ 5).minFac = 5
    exact prime_power_canonical_depth (by norm_num) (by omega)

/-- Canonical depth, both carriers and exact symbolic log/depth weight. -/
theorem event125_packet_checked :
    125 ∈ shellHigherPrimePowerEvents 11 ∧
    (125 : ℕ).factorization (125 : ℕ).minFac = 3 ∧
    3 ∈ shellHigherPrimePowerDepths 11 ∧ 3 ∈ shellOddDepths 11 ∧
    ArithmeticFunction.vonMangoldt 125 = Real.log (125 : ℝ) / 3 := by
  apply event_depth_packet
  · apply mem_shellHigherPrimePowerEvents.mpr
    refine ⟨by norm_num [SquareCell], ?_, by norm_num⟩
    exact (isPrimePow_nat_iff 125).mpr ⟨5, 3, by norm_num, by omega, by norm_num⟩
  · change (5 ^ 3).factorization (5 ^ 3).minFac = 3
    exact prime_power_canonical_depth (by norm_num) (by omega)

/-- Canonical depth, both carriers and exact symbolic log/depth weight. -/
theorem event128_packet_checked :
    128 ∈ shellHigherPrimePowerEvents 11 ∧
    (128 : ℕ).factorization (128 : ℕ).minFac = 7 ∧
    7 ∈ shellHigherPrimePowerDepths 11 ∧ 7 ∈ shellOddDepths 11 ∧
    ArithmeticFunction.vonMangoldt 128 = Real.log (128 : ℝ) / 7 := by
  apply event_depth_packet
  · apply mem_shellHigherPrimePowerEvents.mpr
    refine ⟨by norm_num [SquareCell], ?_, by norm_num⟩
    exact (isPrimePow_nat_iff 128).mpr ⟨2, 7, by norm_num, by omega, by norm_num⟩
  · change (2 ^ 7).factorization (2 ^ 7).minFac = 7
    exact prime_power_canonical_depth (by norm_num) (by omega)

/-- Canonical depth, both carriers and exact symbolic log/depth weight. -/
theorem event8388608_packet_checked :
    8388608 ∈ shellHigherPrimePowerEvents 2896 ∧
    (8388608 : ℕ).factorization (8388608 : ℕ).minFac = 23 ∧
    23 ∈ shellHigherPrimePowerDepths 2896 ∧ 23 ∈ shellOddDepths 2896 ∧
    ArithmeticFunction.vonMangoldt 8388608 = Real.log (8388608 : ℝ) / 23 := by
  apply event_depth_packet
  · apply mem_shellHigherPrimePowerEvents.mpr
    refine ⟨by norm_num [SquareCell], ?_, by norm_num⟩
    exact (isPrimePow_nat_iff 8388608).mpr ⟨2, 23, by norm_num, by omega, by norm_num⟩
  · change (2 ^ 23).factorization (2 ^ 23).minFac = 23
    exact prime_power_canonical_depth (by norm_num) (by omega)

/-- Complete occupied-depth patterns reuse the established event summaries. -/
theorem anchor2_depths_checked : shellHigherPrimePowerDepths 2 = {3} := by
  unfold shellHigherPrimePowerDepths
  rw [SquareShellPrimePowerCalibration.first_cube_shell_checked]
  decide +kernel

theorem anchor5_depths_checked : shellHigherPrimePowerDepths 5 = {3, 5} := by
  unfold shellHigherPrimePowerDepths
  rw [SquareShellPrimePowerCalibration.anchor5_events_checked]
  decide +kernel

theorem anchor11_depths_checked : shellHigherPrimePowerDepths 11 = {3, 7} := by
  unfold shellHigherPrimePowerDepths
  rw [SquareShellPrimePowerCalibration.anchor11_events_checked]
  decide +kernel

/-- A single high odd depth is represented at this larger shell. -/
theorem anchor2896_events_checked : shellHigherPrimePowerEvents 2896 = {8388608} := by
  apply Finset.Subset.antisymm
  · intro q hq
    have e := mem_shellHigherPrimePowerEvents.mp hq
    have c := shell_higher_primePower_canonical e.1 e.2.1 e.2.2
    have hc : SquareCell 2896 (q.minFac ^ q.factorization q.minFac) := by
      rw [← c.2.2.2.1]; exact e.1
    have hb : q.minFac ≤ 203 := by
      by_contra h
      have hp := Nat.pow_le_pow_left (show 204 ≤ q.minFac by omega) 3
      norm_num at hp
      norm_num at c
      omega
    have hex : ∀ p ∈ Nat.primesLE 203, ∀ a ∈ Finset.Icc 3 23,
        2896 ^ 2 < p ^ a ∧ p ^ a < 2897 ^ 2 → p ^ a = 8388608 := by
      decide +kernel
    have hlog : q.factorization q.minFac ≤ 23 := by
      have ht := squareCell_prime_power_exponent_le_log c.1 hc
      norm_num at ht
      exact ht
    have heq := hex _ (Nat.mem_primesLE.mpr ⟨hb, c.1⟩) _
      (Finset.mem_Icc.mpr ⟨c.2.1, hlog⟩) hc
    rw [← c.2.2.2.1] at heq
    exact Finset.mem_singleton.mpr heq
  · intro q hq
    have heq := Finset.mem_singleton.mp hq
    subst q
    exact event8388608_packet_checked.1

theorem anchor2896_depths_checked : shellHigherPrimePowerDepths 2896 = {23} := by
  unfold shellHigherPrimePowerDepths
  rw [anchor2896_events_checked]
  have hd := event8388608_packet_checked.2.1
  simp only [Finset.image_singleton, hd]

/-- Empty depth images at the large preserved anchors are complete certificates. -/
theorem anchor297_depths_checked : shellHigherPrimePowerDepths 297 = ∅ := by
  unfold shellHigherPrimePowerDepths
  rw [SquareShellPrimePowerCalibration.anchor297_events_checked, Finset.image_empty]

theorem anchor1031_depths_checked : shellHigherPrimePowerDepths 1031 = ∅ := by
  unfold shellHigherPrimePowerDepths
  rw [SquareShellPrimePowerCalibration.anchor1031_events_checked, Finset.image_empty]

/-- The finite rational sums are kernel-certified; real-log inequalities are symbolic. -/
theorem anchor5_reciprocal_sum_checked : shellOddDepthReciprocalSum 5 = 8 / 15 := by
  have he : shellOddDepths 5 = {3, 5} := by decide +kernel
  rw [shellOddDepthReciprocalSum, he]
  norm_num

theorem anchor11_reciprocal_sum_checked : shellOddDepthReciprocalSum 11 = 71 / 105 := by
  have he : shellOddDepths 11 = {3, 5, 7} := by decide +kernel
  rw [shellOddDepthReciprocalSum, he]
  norm_num

/-- Occupied and admissible depths are different even at a multiple-event shell. -/
theorem anchor11_occupied_ne_admissible_checked :
    shellHigherPrimePowerDepths 11 ≠ shellOddDepths 11 := by
  rw [anchor11_depths_checked]
  decide +kernel

/-- Exact symbolic prime provider retains its unresolved lower-mass hypothesis. -/
theorem compressed_psi_consumer (n : ℕ) (hn : 3 ≤ n)
    (h : shellHigherPrimePowerLogLogBudget n <
      Chebyshev.psi ((n ^ 2 + 2 * n : ℕ) : ℝ) - Chebyshev.psi ((n ^ 2 : ℕ) : ℝ)) :
    ∃ p, p.Prime ∧ SquareCell n p := exists_prime_squareCell_of_logLogBudget_lt_psi_sub hn h

end DkMathTest.NumberTheory.SquareShellReciprocalCalibration
