/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.GnomonRepeatedCarryPhase

#print "file: DkMath.NumberTheory.Legendre.GnomonQFloorPulse"

namespace DkMath.NumberTheory.Legendre
open scoped BigOperators

/-- Only depth-one prime labels; repeated powers stay on the correction side. -/
def gnomonQPrimeLabels (n : ℕ) : Finset ℕ :=
  (gnomonPascalLargeCarryEvents n).filter Nat.Prime

def gnomonQPrimeBand (n : ℕ) : Finset ℕ :=
  (Finset.Icc (2 * n + 1) (n ^ 2)).filter Nat.Prime

/-- Above the width, the literal natural floor difference is the carry bit. -/
theorem gnomonLargeFloorPulse_eq_carry {n p : ℕ} (hw : 2 * n < p) :
    (n ^ 2 + 2 * n) / p - n ^ 2 / p = gnomonLowDivisorCarryBit n p := by
  change gnomonShellMultipleCount n p = _
  rw [gnomonShellMultipleCount_eq_div_add_carry (by omega), Nat.div_eq_of_lt hw]
  simp

theorem gnomonLargeFloorPulse_binary {n p : ℕ} (hw : 2 * n < p) :
    (n ^ 2 + 2 * n) / p - n ^ 2 / p = 0 ∨
      (n ^ 2 + 2 * n) / p - n ^ 2 / p = 1 := by
  rw [gnomonLargeFloorPulse_eq_carry hw]
  exact gnomonLowDivisorCarryBit_binary n p

/-- The depth-one pulse support, with no prime-power ambiguity. -/
theorem mem_gnomonQPrimeLabels {n p : ℕ} :
    p ∈ gnomonQPrimeLabels n ↔ p ∈ gnomonQPrimeBand n ∧
      (n ^ 2 + 2 * n) / p - n ^ 2 / p = 1 := by
  constructor
  · intro hp
    obtain ⟨hl, hprime⟩ := Finset.mem_filter.mp hp
    obtain ⟨hlo, hw⟩ := Finset.mem_filter.mp hl
    obtain ⟨_, ht, _, hc⟩ := mem_gnomonPascalLowCarryEvents.mp hlo
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, ht⟩, hprime⟩,
      (gnomonLargeFloorPulse_eq_carry hw).trans hc⟩
  · rintro ⟨hp, hc⟩
    obtain ⟨hI, hprime⟩ := Finset.mem_filter.mp hp
    obtain ⟨hw, ht⟩ := Finset.mem_Icc.mp hI
    have hc' : gnomonLowDivisorCarryBit n p = 1 := by
      rw [← gnomonLargeFloorPulse_eq_carry (by omega : 2 * n < p)]
      exact hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨mem_gnomonPascalLowCarryEvents.mpr ⟨hprime.pos, ht,
        (isPrimePow_nat_iff p).mpr ⟨p, 1, hprime, by omega, by simp⟩, hc'⟩, by omega⟩,
        hprime⟩

theorem gnomonQ_eq_prime_label_logs {n : ℕ} (hn : 3 ≤ n) :
    gnomonCofactorWindowMass n = ∑ p ∈ gnomonQPrimeLabels n, Real.log (p : ℝ) := by
  rw [gnomonCofactorWindowMass_eq_singleton hn]
  apply Finset.sum_congr rfl
  intro p hp
  exact ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2

/-- Exact large-prime floor-pulse currency, with repeated powers explicitly excluded. -/
theorem gnomonQ_eq_floor_pulse {n : ℕ} (hn : 3 ≤ n) :
    gnomonCofactorWindowMass n = ∑ p ∈ gnomonQPrimeBand n,
      Real.log (p : ℝ) * (((n ^ 2 + 2 * n) / p - n ^ 2 / p : ℕ) : ℝ) := by
  rw [gnomonQ_eq_prime_label_logs hn]
  calc
    _ = ∑ p ∈ gnomonQPrimeLabels n,
        Real.log (p : ℝ) * (((n ^ 2 + 2 * n) / p - n ^ 2 / p : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [(mem_gnomonQPrimeLabels.mp hp).2]
      simp
    _ = _ := by
      apply Finset.sum_subset (fun p hp => (mem_gnomonQPrimeLabels.mp hp).1)
      intro p hp hnot
      have hw := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
      have hc0 : (n ^ 2 + 2 * n) / p - n ^ 2 / p = 0 := by
        rcases gnomonLargeFloorPulse_binary (by omega : 2 * n < p) with h | h
        · exact h
        · exact (hnot (mem_gnomonQPrimeLabels.mpr ⟨hp, h⟩)).elim
      simp [hc0]

/-- Every Q label has a shell target and a cofactor in the full coupled window family. -/
theorem gnomonQPrimeLabel_packet {n p : ℕ} (hn : 3 ≤ n) (hp : p ∈ gnomonQPrimeLabels n) :
    p.Prime ∧ 2 * n < p ∧ SquareCell n (gnomonNextShellMultiple n p) ∧
      2 ≤ n ^ 2 / p + 1 ∧ n ^ 2 / p + 1 < n := by
  have hprime := (Finset.mem_filter.mp hp).2
  have hlarge := Finset.mem_filter.mp (Finset.mem_filter.mp hp).1
  have hlow := mem_gnomonPascalLowCarryEvents.mp hlarge.1
  have hk := gnomonSingletonCarry_cofactor_window hn hp
  exact ⟨hprime, hlarge.2, (gnomonNextShellMultiple_packet hlarge.2 hlow.2.2.2).1,
    (Finset.mem_Icc.mp hk.1).1, gnomonNextShellMultiple_cofactor_lt hn hlarge.2⟩

/-- Unlike repeated powers, distinct Q prime labels cannot collide at one shell target. -/
theorem gnomonQPrimeTarget_injective {n : ℕ} (hn : 3 ≤ n) :
    Set.InjOn (gnomonNextShellMultiple n) (↑(gnomonQPrimeLabels n)) := by
  intro p hp q hq he
  have h := gnomonQPrimeLabel_packet hn hp
  have h' := gnomonQPrimeLabel_packet hn hq
  have hd : p ∣ gnomonNextShellMultiple n p := by
    unfold gnomonNextShellMultiple
    exact dvd_mul_right _ _
  have hd' : q ∣ gnomonNextShellMultiple n p := by
    rw [he]
    unfold gnomonNextShellMultiple
    exact dvd_mul_right _ _
  exact gnomonLarge_prime_power_divisors_same_base hn h.2.2.1 h.1 h'.1
    (by simpa using h.2.1 : 2 * n < p ^ 1)
    (by simpa using h'.2.1 : 2 * n < q ^ 1)
    (by simpa using hd : p ^ 1 ∣ gnomonNextShellMultiple n p)
    (by simpa using hd' : q ^ 1 ∣ gnomonNextShellMultiple n p)

/-- Exact selected-target product identity; this alone is not an independent estimate. -/
theorem gnomonQ_target_cofactor_product (n : ℕ) :
    (∏ p ∈ gnomonQPrimeLabels n, p) *
      (∏ p ∈ gnomonQPrimeLabels n, (n ^ 2 / p + 1)) =
      ∏ p ∈ gnomonQPrimeLabels n, gnomonNextShellMultiple n p := by
  unfold gnomonNextShellMultiple
  exact (Finset.prod_mul_distrib (s := gnomonQPrimeLabels n)
    (f := fun p : ℕ => p) (g := fun p : ℕ => n ^ 2 / p + 1)).symm

/-- One global target-capacity envelope, using only endpoints and the minimum cofactor two. -/
noncomputable def gnomonQTargetCapacityBudget (n : ℕ) : ℝ :=
  ∑ y ∈ (Finset.Icc (n ^ 2 + 1) (n ^ 2 + 2 * n) : Finset ℕ),
    (Real.log (y : ℝ) - Real.log 2)

/-- Target injection couples all quotient windows; no wheel survivors are enumerated. -/
theorem gnomonQ_le_targetCapacity {n : ℕ} (hn : 3 ≤ n) :
    gnomonCofactorWindowMass n ≤ gnomonQTargetCapacityBudget n := by
  rw [gnomonQ_eq_prime_label_logs hn]
  have hpoint : ∀ p ∈ gnomonQPrimeLabels n,
      Real.log (p : ℝ) ≤ Real.log (gnomonNextShellMultiple n p : ℝ) - Real.log 2 := by
    intro p hp
    have h := gnomonQPrimeLabel_packet hn hp
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast h.1.ne_zero
    have hk0 : ((n ^ 2 / p + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hk2 : (2 : ℝ) ≤ ((n ^ 2 / p + 1 : ℕ) : ℝ) := by exact_mod_cast h.2.2.2.1
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hk2
    have he : Real.log (gnomonNextShellMultiple n p : ℝ) =
        Real.log (p : ℝ) + Real.log ((n ^ 2 / p + 1 : ℕ) : ℝ) := by
      unfold gnomonNextShellMultiple
      rw [Nat.cast_mul, Real.log_mul hp0 hk0]
    linarith
  have hsub : (gnomonQPrimeLabels n).image (gnomonNextShellMultiple n) ⊆
      Finset.Icc (n ^ 2 + 1) (n ^ 2 + 2 * n) := by
    intro y hy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
    have h := (gnomonQPrimeLabel_packet hn hp).2.2.1
    exact Finset.mem_Icc.mpr ⟨by have := h.1; omega, by have := h.2; nlinarith⟩
  calc
    _ ≤ ∑ p ∈ gnomonQPrimeLabels n,
        (Real.log (gnomonNextShellMultiple n p : ℝ) - Real.log 2) := Finset.sum_le_sum hpoint
    _ = ∑ y ∈ (gnomonQPrimeLabels n).image (gnomonNextShellMultiple n),
        (Real.log (y : ℝ) - Real.log 2) :=
      (Finset.sum_image (f := fun y : ℕ => Real.log (y : ℝ) - Real.log 2)
        (gnomonQPrimeTarget_injective hn)).symm
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro y hy _
      have hlo := (Finset.mem_Icc.mp hy).1
      have hy2 : (2 : ℝ) ≤ y := by
        have : 2 ≤ y := by nlinarith
        exact_mod_cast this
      exact sub_nonneg.mpr (Real.log_le_log (by norm_num) hy2)

/-- The independent capacity has an explicit factorial normalization penalty. -/
theorem gnomonQTargetCapacity_eq_factorial_penalty {n : ℕ} (hn : 1 ≤ n) :
    gnomonQTargetCapacityBudget n = Real.log (GnomonPascalCell n : ℝ) +
      Real.log ((2 * n).factorial : ℝ) - ((2 * n : ℕ) : ℝ) * Real.log 2 := by
  unfold gnomonQTargetCapacityBudget
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    ← gnomonPascalCell_log_add_factorial_eq_shell_log n hn]
  have hc : (Finset.Icc (n ^ 2 + 1) (n ^ 2 + 2 * n)).card = 2 * n := by
    rw [Nat.card_Icc]
    omega
  rw [hc]

/-- Whole-target capacity cannot pay the factorial normalization even before correction. -/
theorem gnomonShellFactorial_ge_two_power {n : ℕ} (hn : 3 ≤ n) :
    2 ^ (2 * n) ≤ (2 * n).factorial := by
  induction n, hn using Nat.le_induction with
  | base => decide +kernel
  | succ n hn ih =>
    have hp : 4 ≤ (2 * n + 1) * (2 * n + 2) := by nlinarith
    calc
      2 ^ (2 * (n + 1)) = 2 ^ (2 * n) * 4 := by
        rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
        norm_num
      _ ≤ (2 * n).factorial * ((2 * n + 1) * (2 * n + 2)) := Nat.mul_le_mul ih hp
      _ = (2 * (n + 1)).factorial := by
        rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega, Nat.factorial_succ,
          Nat.factorial_succ]
        ring

/-- A global obstruction for this particular envelope, not for the exact Q inequality. -/
theorem gnomonQTargetCapacity_ge_log_cell {n : ℕ} (hn : 3 ≤ n) :
    Real.log (GnomonPascalCell n : ℝ) ≤ gnomonQTargetCapacityBudget n := by
  have hp := gnomonShellFactorial_ge_two_power hn
  have hpR : (2 : ℝ) ^ (2 * n) ≤ ((2 * n).factorial : ℝ) := by exact_mod_cast hp
  have hl := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ (2 * n)) hpR
  rw [Real.log_pow] at hl
  rw [gnomonQTargetCapacity_eq_factorial_penalty (by omega : 1 ≤ n)]
  linarith

private theorem correction_nonneg (n : ℕ) : 0 ≤ gnomonNonSingletonCorrection n := by
  have hs : 0 ≤ gnomonPascalSmallCarryMass n :=
    Finset.sum_nonneg (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  have hr : 0 ≤ gnomonRepeatedCarryMass n :=
    Finset.sum_nonneg (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  have hh := gnomonPascalShellHigherPrimePowerMass_nonneg n
  unfold gnomonNonSingletonCorrection
  linarith

/-- The tested global capacity route is incapable of closing 040 at any anchor n>=3. -/
theorem gnomonQTargetCapacity_never_closes040 {n : ℕ} (hn : 3 ≤ n) :
    ¬ gnomonQTargetCapacityBudget n + gnomonRepeatPhaseCorrectionBudget n <
      Real.log (GnomonPascalCell n : ℝ) := by
  have hu := gnomonQTargetCapacity_ge_log_cell hn
  have hb := gnomonNonSingletonCorrection_le_repeatPhaseBudget hn
  have hc := correction_nonneg n
  linarith

end DkMath.NumberTheory.Legendre
