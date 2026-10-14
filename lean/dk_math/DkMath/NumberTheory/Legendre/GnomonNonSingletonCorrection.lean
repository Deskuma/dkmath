/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.GnomonCofactorAdaptiveRoughness
import Mathlib.NumberTheory.Chebyshev

#print "file: DkMath.NumberTheory.Legendre.GnomonNonSingletonCorrection"

namespace DkMath.NumberTheory.Legendre
open scoped BigOperators

noncomputable def gnomonNonSingletonCorrection (n : ℕ) : ℝ :=
  gnomonPascalSmallCarryMass n + gnomonRepeatedCarryMass n +
    gnomonPascalShellHigherPrimePowerMass n

/-- Global prefix masses, with no shell inventory or carry-phase test. -/
noncomputable def gnomonNonSingletonBudget (n : ℕ) : ℝ :=
  Chebyshev.theta (2 * n) + (Chebyshev.psi ((n : ℝ) ^ 2) -
    Chebyshev.theta ((n : ℝ) ^ 2)) + shellHigherPrimePowerReciprocalBudget n

theorem gnomonPascalSmallCarryMass_le_psi (n : ℕ) :
    gnomonPascalSmallCarryMass n ≤ Chebyshev.psi (2 * n) := by
  unfold gnomonPascalSmallCarryMass
  rw [Chebyshev.psi_eq_sum_Icc]
  have he : (2 : ℝ) * (n : ℝ) = ((2 * n : ℕ) : ℝ) := by norm_cast
  rw [he, Nat.floor_natCast]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    obtain ⟨_, hdle⟩ := Finset.mem_filter.mp hd
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, hdle⟩
  · intro d _ _
    exact ArithmeticFunction.vonMangoldt_nonneg

private theorem nonprime_prefix (N : ℕ) :
    (∑ d ∈ (Finset.Icc 0 N).filter (fun d => ¬ d.Prime),
      ArithmeticFunction.vonMangoldt d) = Chebyshev.psi N - Chebyshev.theta N := by
  rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast]
  have he := Finset.sum_filter_add_sum_filter_not (Finset.Icc 0 N) Nat.Prime
    (fun d => ArithmeticFunction.vonMangoldt d)
  have hp : (∑ d ∈ (Finset.Icc 0 N).filter Nat.Prime,
      ArithmeticFunction.vonMangoldt d) =
      ∑ d ∈ (Finset.Icc 0 N).filter Nat.Prime, Real.log (d : ℝ) := by
    apply Finset.sum_congr rfl
    intro d hd
    exact ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hd).2
  rw [hp] at he
  linarith

theorem gnomonRepeatedCarryMass_le_globalCorrection (n : ℕ) :
    gnomonRepeatedCarryMass n ≤ Chebyshev.psi ((n : ℝ) ^ 2) -
      Chebyshev.theta ((n : ℝ) ^ 2) := by
  rw [← Nat.cast_pow, ← nonprime_prefix]
  unfold gnomonRepeatedCarryMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    obtain ⟨hdL, hdP⟩ := Finset.mem_filter.mp hd
    have hdLow := (Finset.mem_filter.mp hdL).1
    have hdN := (mem_gnomonPascalLowCarryEvents.mp hdLow).2.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, hdN⟩, hdP⟩
  · intro d _ _
    exact ArithmeticFunction.vonMangoldt_nonneg

private theorem carry_bands_le_prefix (n : ℕ) :
    gnomonPascalSmallCarryMass n + gnomonRepeatedCarryMass n ≤
      Chebyshev.theta (2 * n) +
        (Chebyshev.psi ((n : ℝ) ^ 2) - Chebyshev.theta ((n : ℝ) ^ 2)) := by
  let A := gnomonPascalSmallCarryEvents n
  let R := (gnomonPascalLargeCarryEvents n).filter (fun d => ¬ d.Prime)
  let P := (Finset.Icc 0 (2 * n)).filter Nat.Prime
  let T := (Finset.Icc 0 (n ^ 2)).filter (fun d => ¬ d.Prime)
  have hAR : Disjoint A R := by
    apply Finset.disjoint_left.mpr
    intro d ha hr
    have hlo := (Finset.mem_filter.mp ha).2
    have hhi := (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2
    omega
  have hPT : Disjoint P T := by
    apply Finset.disjoint_left.mpr
    intro d hp ht
    exact (Finset.mem_filter.mp ht).2 (Finset.mem_filter.mp hp).2
  have hsub : A ∪ R ⊆ P ∪ T := by
    intro d hd
    rcases Finset.mem_union.mp hd with ha | hr
    · obtain ⟨hlow, hle⟩ := Finset.mem_filter.mp ha
      by_cases hp : d.Prime
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, hle⟩, hp⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _,
            (mem_gnomonPascalLowCarryEvents.mp hlow).2.1⟩, hp⟩)
    · obtain ⟨hl, hp⟩ := Finset.mem_filter.mp hr
      have hlow := (Finset.mem_filter.mp hl).1
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _,
          (mem_gnomonPascalLowCarryEvents.mp hlow).2.1⟩, hp⟩)
  have h := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun d _ _ => ArithmeticFunction.vonMangoldt_nonneg (n := d))
  rw [Finset.sum_union hAR, Finset.sum_union hPT] at h
  have hp : (∑ d ∈ P, ArithmeticFunction.vonMangoldt d) = Chebyshev.theta (2 * n) := by
    rw [Chebyshev.theta_eq_sum_Icc]
    have he : (2 : ℝ) * n = ((2 * n : ℕ) : ℝ) := by norm_cast
    rw [he, Nat.floor_natCast]
    apply Finset.sum_congr rfl
    intro d hd
    exact ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hd).2
  have ht : (∑ d ∈ T, ArithmeticFunction.vonMangoldt d) =
      Chebyshev.psi ((n : ℝ) ^ 2) - Chebyshev.theta ((n : ℝ) ^ 2) := by
    rw [← Nat.cast_pow]
    exact nonprime_prefix (n ^ 2)
  rw [hp, ht] at h
  exact h

/-- The small and repeated bands charge disjoint nonprime labels; low powers are not doubled. -/
theorem gnomonNonSingletonCorrection_le_budget {n : ℕ} (hn : 3 ≤ n) :
    gnomonNonSingletonCorrection n ≤ gnomonNonSingletonBudget n := by
  have hc := carry_bands_le_prefix n
  have hh := gnomonPascalShellHigherPrimePowerMass_le_reciprocalBudget hn
  unfold gnomonNonSingletonCorrection gnomonNonSingletonBudget
  linarith

/-- An explicit prefix-only scale bound: its main size is linear in n. -/
theorem gnomonNonSingletonBudget_le_explicit (n : ℕ) :
    gnomonNonSingletonBudget n ≤
      Real.log 4 * (2 * n) + (Real.log 4 + 4) * (((n : ℝ) ^ 2) ^ (2 : ℝ)⁻¹ +
        ((n : ℝ) ^ 2) ^ (3 : ℝ)⁻¹ + ((n : ℝ) ^ 2) ^ (5 : ℝ)⁻¹) +
      shellHigherPrimePowerReciprocalBudget n := by
  have hs := Chebyshev.theta_le_log4_mul_x (x := 2 * n) (by positivity)
  have hr := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi ((n : ℝ) ^ 2)
  have h2 := Chebyshev.psi_le_const_mul_self (x := ((n : ℝ) ^ 2) ^ (2 : ℝ)⁻¹)
    (by positivity)
  have h3 := Chebyshev.psi_le_const_mul_self (x := ((n : ℝ) ^ 2) ^ (3 : ℝ)⁻¹)
    (by positivity)
  have h5 := Chebyshev.psi_le_const_mul_self (x := ((n : ℝ) ^ 2) ^ (5 : ℝ)⁻¹)
    (by positivity)
  unfold gnomonNonSingletonBudget
  nlinarith

theorem gnomonPascalOldLogBudget_eq_singleton_add_correction {n : ℕ} (hn : 3 ≤ n) :
    gnomonPascalOldLogBudget n = gnomonCofactorWindowMass n +
      gnomonNonSingletonCorrection n := by
  have h := gnomonPascalOldLogBudget_adaptive_eq hn
  rw [gnomonCofactorAdaptive_budget_eq hn] at h
  unfold gnomonNonSingletonCorrection
  linarith

/-- Sufficient provider; replacing exact correction by an upper bound is not an equivalence. -/
theorem exists_prime_squareCell_of_nonSingletonBudget_lt {n : ℕ} (hn : 3 ≤ n)
    (hstrict : gnomonCofactorWindowMass n + gnomonNonSingletonBudget n <
      Real.log (GnomonPascalCell n : ℝ)) : ∃ p, p.Prime ∧ SquareCell n p := by
  apply (gnomonPascalOldLogBudget_lt_iff hn).mp
  rw [gnomonPascalOldLogBudget_eq_singleton_add_correction hn]
  have h := gnomonNonSingletonCorrection_le_budget hn
  linarith

end DkMath.NumberTheory.Legendre
