/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.GnomonCofactorThreePrime
import DkMathTest.NumberTheory.GnomonCofactorSemiprimeCalibration

#print "file: DkMathTest.NumberTheory.GnomonCofactorThreePrimeCalibration"

namespace DkMathTest.NumberTheory.GnomonCofactorThreePrimeCalibration

open DkMath.NumberTheory.Legendre DkMath.NumberTheory.PrimorialUniverse
open scoped BigOperators

private def basis : Finset ℕ := {2, 3, 5}

private theorem basis_prime : IsFinitePrimeBasis basis := by
  intro p hp
  simp only [basis, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl <;> norm_num

private theorem basis_bound {n : ℕ} (hn : 3 ≤ n) : ∀ p ∈ basis, p ≤ 2 * n := by
  intro p hp
  simp only [basis, Finset.mem_insert, Finset.mem_singleton] at hp
  omega

private def sieveProduct (n : ℕ) (S : Finset ℕ) : ℕ :=
  ∏ k ∈ Finset.Icc 2 (n - 1), ∏ q ∈ gnomonCofactorSieveCandidates n k S, q

private theorem sieve_log_product (n : ℕ) (S : Finset ℕ) :
    gnomonCofactorSieveMass n S = Real.log (sieveProduct n S : ℝ) := by
  unfold gnomonCofactorSieveMass sieveProduct
  rw [Nat.cast_prod, Real.log_prod]
  · apply Finset.sum_congr rfl
    intro k _
    rw [Nat.cast_prod, Real.log_prod]
    intro q hq
    have h := Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1
    exact_mod_cast (show q ≠ 0 by omega)
  · intro k _
    rw [Nat.cast_ne_zero]
    apply Finset.prod_ne_zero_iff.mpr
    intro q hq
    have h := Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1
    omega

private def residualProduct (n : ℕ) : ℕ :=
  (∏ d ∈ gnomonPascalSmallCarryEvents n, d.minFac) *
  (∏ d ∈ (gnomonPascalLargeCarryEvents n).filter (fun d => ¬ d.Prime), d.minFac) *
  (∏ d ∈ shellHigherPrimePowerEvents n, d.minFac)

private theorem minFac_product_ne_zero (s : Finset ℕ) :
    ((∏ d ∈ s, d.minFac : ℕ) : ℝ) ≠ 0 := by
  have h : 0 < ∏ d ∈ s, d.minFac := Finset.prod_pos (fun d _ => Nat.minFac_pos d)
  exact_mod_cast h.ne'

private theorem prime_power_sum_log_product {s : Finset ℕ}
    (hs : ∀ d ∈ s, IsPrimePow d) :
    (∑ d ∈ s, ArithmeticFunction.vonMangoldt d) =
      Real.log ((∏ d ∈ s, d.minFac : ℕ) : ℝ) := by
  rw [Nat.cast_prod, Real.log_prod]
  · apply Finset.sum_congr rfl
    intro d hd
    simp only [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (hs d hd)]
  · intro d _
    exact_mod_cast (Nat.minFac_pos d).ne'

private theorem residual_log_product (n : ℕ) :
    gnomonPascalSmallCarryMass n + gnomonRepeatedCarryMass n +
      gnomonPascalShellHigherPrimePowerMass n = Real.log (residualProduct n : ℝ) := by
  have hs : ∀ d ∈ gnomonPascalSmallCarryEvents n, IsPrimePow d := by
    intro d hd
    exact (mem_gnomonPascalLowCarryEvents.mp (Finset.mem_filter.mp hd).1).2.2.1
  have hr : ∀ d ∈ (gnomonPascalLargeCarryEvents n).filter (fun d => ¬ d.Prime),
      IsPrimePow d := by
    intro d hd
    exact (mem_gnomonPascalLowCarryEvents.mp
      (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).1).2.2.1
  have hh : ∀ d ∈ shellHigherPrimePowerEvents n, IsPrimePow d := by
    intro d hd
    exact (mem_shellHigherPrimePowerEvents.mp hd).2.1
  rw [gnomonPascalSmallCarryMass, gnomonRepeatedCarryMass,
    gnomonPascalShellHigherPrimePowerMass_eq_events,
    prime_power_sum_log_product hs, prime_power_sum_log_product hr,
    prime_power_sum_log_product hh]
  unfold residualProduct
  simp only [Nat.cast_mul]
  rw [Real.log_mul (mul_ne_zero (minFac_product_ne_zero _) (minFac_product_ne_zero _))
    (minFac_product_ne_zero _),
    Real.log_mul (minFac_product_ne_zero _) (minFac_product_ne_zero _)]

private theorem residual_pos (n : ℕ) : 0 < residualProduct n := by
  unfold residualProduct
  apply Nat.mul_pos
  · apply Nat.mul_pos <;> exact Finset.prod_pos (fun d _ => Nat.minFac_pos d)
  · exact Finset.prod_pos (fun d _ => Nat.minFac_pos d)

private theorem sieve_pos (n : ℕ) (S : Finset ℕ) : 0 < sieveProduct n S := by
  apply Finset.prod_pos
  intro k _
  apply Finset.prod_pos
  intro q hq
  have h := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
  omega

private def combinedProduct (n : ℕ) (S : Finset ℕ) : ℕ :=
  ∏ k ∈ Finset.Icc 2 (n - 1), ∏ q ∈ gnomonCofactorThreePrimeCombinedWitnesses n k S, q

private theorem combined_pos (n : ℕ) (S : Finset ℕ) : 0 < combinedProduct n S := by
  apply Finset.prod_pos
  intro k _
  apply Finset.prod_pos
  intro q hq
  have hc := gnomonCofactorThreePrimeCombined_subset_error n k S hq
  have h := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).1).1
  omega

private theorem combined_log_product (n : ℕ) (S : Finset ℕ) :
    gnomonCofactorThreePrimeCombinedMass n S = Real.log (combinedProduct n S : ℝ) := by
  unfold gnomonCofactorThreePrimeCombinedMass combinedProduct
  rw [Nat.cast_prod, Real.log_prod]
  · apply Finset.sum_congr rfl
    intro k _
    rw [Nat.cast_prod, Real.log_prod]
    intro q hq
    have hc := gnomonCofactorThreePrimeCombined_subset_error n k S hq
    have h := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).1).1
    exact_mod_cast (show q ≠ 0 by omega)
  · intro k _
    rw [Nat.cast_ne_zero]
    apply Finset.prod_ne_zero_iff.mpr
    intro q hq
    have hc := gnomonCofactorThreePrimeCombined_subset_error n k S hq
    have h := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).1).1
    omega

/-- Repeated prime factors are admitted without ambiguous ordering. -/
theorem triples32_checked : ∀ k ∈ Finset.Icc 2 31,
    gnomonCofactorThreePrimeTriples 32 k {2, 3, 5} =
      if k = 2 then {(7, 7, 11)} else if k = 3 then {(7, 7, 7)} else ∅ := by
  decide +kernel

/-- Both explicit higher-composite regressions are new witnesses. -/
theorem witnesses32_checked :
    539 ∈ gnomonCofactorThreePrimeWitnesses 32 2 {2, 3, 5} ∧
    343 ∈ gnomonCofactorThreePrimeWitnesses 32 3 {2, 3, 5} := by decide +kernel

/-- The earlier small witnesses and all the 32 residual are covered exactly. -/
theorem complete_small_carriers_checked : ∀ n ∈ ({9, 12, 31, 32} : Finset ℕ),
    ∀ k ∈ Finset.Icc 2 (n - 1), gnomonCofactorThreePrimeCombinedWitnesses n k {2, 3, 5} =
      (gnomonCofactorSieveCandidates n k {2, 3, 5}).filter (fun q => ¬ q.Prime) := by
  decide +kernel

theorem exact_small_budgets_checked : ∀ n ∈ ({9, 12, 31, 32} : Finset ℕ),
    gnomonCofactorThreePrimeBudget n {2, 3, 5} = gnomonCofactorWindowMass n := by
  intro n hn
  have hn3 : 3 ≤ n := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    omega
  have hd : gnomonCofactorThreePrimeCombinedMass n {2, 3, 5} =
      gnomonCofactorSieveCompositeError n {2, 3, 5} := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [complete_small_carriers_checked n hn k hk]
  have he := gnomonCofactorSieveMass_eq_window_add_error basis_prime (basis_bound hn3)
  simp only [basis] at he
  apply le_antisymm
  · have hu := min_le_right (gnomonCofactorSemiprimeBudget n {2, 3, 5})
      (gnomonCofactorSieveMass n {2, 3, 5} - gnomonCofactorThreePrimeCombinedMass n {2, 3, 5})
    change gnomonCofactorThreePrimeBudget n {2, 3, 5} ≤ _ at hu
    linarith
  · exact gnomonCofactorWindowMass_le_threePrimeBudget hn3 basis_prime (basis_bound hn3)

/-- The known semiprime consumer remains valid. -/
theorem consumer31_checked :
    gnomonPascalSmallCarryMass 31 + gnomonRepeatedCarryMass 31 +
      gnomonCofactorThreePrimeBudget 31 {2, 3, 5} + gnomonPascalShellHigherPrimePowerMass 31 <
        Real.log (GnomonPascalCell 31 : ℝ) := by
  have h := DkMathTest.NumberTheory.GnomonCofactorSemiprimeCalibration.consumer31_checked
  have hu := gnomonCofactorThreePrimeBudget_le_semiprimeBudget 31 {2, 3, 5}
  linarith

/-- A four-factor survivor remains: the finite witness is not full composite classification. -/
theorem fourth_power69_checked :
    2401 ∈ gnomonCofactorSieveCandidates 69 2 {2, 3, 5} ∧
    2401 = (7 : ℕ) ^ 4 ∧
    2401 ∉ gnomonCofactorThreePrimeCombinedWitnesses 69 2 {2, 3, 5} := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Exact kernel products and the binomial cell at 32 require this finite budget.
theorem products32_checked :
    0 < residualProduct 32 * sieveProduct 32 {2, 3, 5} ∧
    residualProduct 32 * sieveProduct 32 {2, 3, 5} <
      GnomonPascalCell 32 * combinedProduct 32 {2, 3, 5} := by
  unfold GnomonPascalCell
  rw [Nat.choose_eq_fast_choose]
  decide +kernel

set_option maxRecDepth 10000 in
-- Cast normalization of the certified finite products requires this recursion budget.
theorem consumer32_checked :
    gnomonPascalSmallCarryMass 32 + gnomonRepeatedCarryMass 32 +
      gnomonCofactorThreePrimeBudget 32 {2, 3, 5} + gnomonPascalShellHigherPrimePowerMass 32 <
        Real.log (GnomonPascalCell 32 : ℝ) := by
  have hp : (0 : ℝ) < (residualProduct 32 : ℝ) * (sieveProduct 32 {2, 3, 5} : ℝ) := by
    exact_mod_cast products32_checked.1
  have hc : (residualProduct 32 : ℝ) * (sieveProduct 32 {2, 3, 5} : ℝ) <
      (GnomonPascalCell 32 : ℝ) * (combinedProduct 32 {2, 3, 5} : ℝ) := by
    exact_mod_cast products32_checked.2
  have h := Real.log_lt_log hp hc
  have hr0 : (residualProduct 32 : ℝ) ≠ 0 := by exact_mod_cast (residual_pos 32).ne'
  have hv0 : (sieveProduct 32 {2, 3, 5} : ℝ) ≠ 0 := by exact_mod_cast (sieve_pos 32 {2, 3, 5}).ne'
  have hc0 : (GnomonPascalCell 32 : ℝ) ≠ 0 := by
    exact_mod_cast ((Nat.choose_pos (by norm_num : 64 ≤ 1088)) : 0 < GnomonPascalCell 32).ne'
  have hd0 : (combinedProduct 32 {2, 3, 5} : ℝ) ≠ 0 := by exact_mod_cast (combined_pos 32 {2, 3, 5}).ne'
  rw [Real.log_mul hr0 hv0, Real.log_mul hc0 hd0] at h
  have hR := residual_log_product 32
  have hV := sieve_log_product 32 {2, 3, 5}
  have hD := combined_log_product 32 {2, 3, 5}
  have hu := min_le_right (gnomonCofactorSemiprimeBudget 32 {2, 3, 5})
    (gnomonCofactorSieveMass 32 {2, 3, 5} - gnomonCofactorThreePrimeCombinedMass 32 {2, 3, 5})
  change gnomonCofactorThreePrimeBudget 32 {2, 3, 5} ≤ _ at hu
  linarith

/-- Equality at the first admissible anchor prevents a universal strict gain. -/
theorem equality3_checked : gnomonCofactorThreePrimeBudget 3 {2, 3, 5} =
    gnomonCofactorSemiprimeBudget 3 {2, 3, 5} := by
  have hd : gnomonCofactorThreePrimeCombinedMass 3 {2, 3, 5} = 0 := by
    rw [combined_log_product]
    have h : combinedProduct 3 {2, 3, 5} = 1 := by decide +kernel
    rw [h]
    norm_num
  unfold gnomonCofactorThreePrimeBudget
  rw [hd, sub_zero]
  exact min_eq_left ((gnomonCofactorSemiprimeBudget_le_leastFactorBudget _ _).trans
    ((gnomonCofactorLeastFactorBudget_le_sieveBudget _ _).trans (min_le_right _ _)))

end DkMathTest.NumberTheory.GnomonCofactorThreePrimeCalibration
