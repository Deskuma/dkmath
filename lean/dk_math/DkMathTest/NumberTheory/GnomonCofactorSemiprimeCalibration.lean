/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.GnomonCofactorSemiprime
import DkMathTest.NumberTheory.GnomonCofactorLeastFactorCalibration

#print "file: DkMathTest.NumberTheory.GnomonCofactorSemiprimeCalibration"

namespace DkMathTest.NumberTheory.GnomonCofactorSemiprimeCalibration

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

private def semiprimeProduct (n : ℕ) (S : Finset ℕ) : ℕ :=
  ∏ k ∈ Finset.Icc 2 (n - 1), ∏ q ∈ gnomonCofactorSemiprimeWitnesses n k S, q

private theorem semiprimeProduct_pos (n : ℕ) (S : Finset ℕ) : 0 < semiprimeProduct n S := by
  apply Finset.prod_pos
  intro k _
  apply Finset.prod_pos
  intro q hq
  have hc := gnomonCofactorSemiprimeWitnesses_subset_error n k S hq
  have h := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).1).1
  omega

private theorem semiprime_log_product (n : ℕ) (S : Finset ℕ) :
    gnomonCofactorSemiprimeMass n S = Real.log (semiprimeProduct n S : ℝ) := by
  unfold gnomonCofactorSemiprimeMass semiprimeProduct
  rw [Nat.cast_prod, Real.log_prod]
  · apply Finset.sum_congr rfl
    intro k _
    rw [Nat.cast_prod, Real.log_prod]
    intro q hq
    have hc := gnomonCofactorSemiprimeWitnesses_subset_error n k S hq
    have h := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).1).1
    exact_mod_cast (show q ≠ 0 by omega)
  · intro k _
    rw [Nat.cast_ne_zero]
    apply Finset.prod_ne_zero_iff.mpr
    intro q hq
    have hc := gnomonCofactorSemiprimeWitnesses_subset_error n k S hq
    have h := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).1).1
    omega

/-- Both the square and distinct-prime product are independently certified. -/
theorem witnesses9_12_checked :
    (7, 7) ∈ gnomonCofactorSemiprimePairs 9 2 {2, 3, 5} ∧
    49 ∈ gnomonCofactorSemiprimeWitnesses 9 2 {2, 3, 5} ∧
    (7, 11) ∈ gnomonCofactorSemiprimePairs 12 2 {2, 3, 5} ∧
    77 ∈ gnomonCofactorSemiprimeWitnesses 12 2 {2, 3, 5} := by decide +kernel

/-- At the four required small anchors every surviving composite is semiprime. -/
theorem complete_small_carriers_checked : ∀ n ∈ ({9, 12, 29, 31} : Finset ℕ),
    ∀ k ∈ Finset.Icc 2 (n - 1), gnomonCofactorSemiprimeWitnesses n k {2, 3, 5} =
      (gnomonCofactorSieveCandidates n k {2, 3, 5}).filter (fun q => ¬ q.Prime) := by
  decide +kernel

theorem exact_small_budgets_checked : ∀ n ∈ ({9, 12, 29, 31} : Finset ℕ),
    gnomonCofactorSemiprimeBudget n {2, 3, 5} = gnomonCofactorWindowMass n := by
  intro n hn
  have hn3 : 3 ≤ n := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    omega
  have hd : gnomonCofactorSemiprimeMass n {2, 3, 5} =
      gnomonCofactorSieveCompositeError n {2, 3, 5} := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [complete_small_carriers_checked n hn k hk]
  have he := gnomonCofactorSieveMass_eq_window_add_error basis_prime (basis_bound hn3)
  simp only [basis] at he
  apply le_antisymm
  · have hu := min_le_right (gnomonCofactorLeastFactorBudget n {2, 3, 5})
      (gnomonCofactorSieveMass n {2, 3, 5} - gnomonCofactorSemiprimeMass n {2, 3, 5})
    change gnomonCofactorSemiprimeBudget n {2, 3, 5} ≤ _ at hu
    linarith
  · exact gnomonCofactorWindowMass_le_semiprimeBudget hn3 basis_prime (basis_bound hn3)

/-- The former double factorization is preserved, but neither composite complement is admitted. -/
theorem collision539_checked :
    (7, 77) ∈ gnomonCofactorFactorPairs 32 2 {2, 3, 5} ∧
    (11, 49) ∈ gnomonCofactorFactorPairs 32 2 {2, 3, 5} ∧
    (7, 77) ∉ gnomonCofactorSemiprimePairs 32 2 {2, 3, 5} ∧
    (11, 49) ∉ gnomonCofactorSemiprimePairs 32 2 {2, 3, 5} ∧
    539 ∉ gnomonCofactorSemiprimeWitnesses 32 2 {2, 3, 5} := by decide +kernel

/-- The remaining carrier at 32 has one cube and one three-factor product. -/
theorem residual32_carrier_checked : ∀ k ∈ Finset.Icc 2 31,
    ((gnomonCofactorSieveCandidates 32 k {2, 3, 5}).filter (fun q => ¬ q.Prime)) \
      gnomonCofactorSemiprimeWitnesses 32 k {2, 3, 5} =
        if k = 2 then {539} else if k = 3 then {343} else ∅ := by decide +kernel

theorem consumer29_checked :
    gnomonPascalSmallCarryMass 29 + gnomonRepeatedCarryMass 29 +
      gnomonCofactorSemiprimeBudget 29 {2, 3, 5} + gnomonPascalShellHigherPrimePowerMass 29 <
        Real.log (GnomonPascalCell 29 : ℝ) := by
  have h := DkMathTest.NumberTheory.GnomonCofactorLeastFactorCalibration.consumer29_checked
  have hu := gnomonCofactorSemiprimeBudget_le_leastFactorBudget 29 {2, 3, 5}
  linarith

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Kernel evaluation of the finite 31 products and binomial cell needs this budget.
theorem products31_checked :
    0 < residualProduct 31 * sieveProduct 31 {2, 3, 5} ∧
    residualProduct 31 * sieveProduct 31 {2, 3, 5} <
      GnomonPascalCell 31 * semiprimeProduct 31 {2, 3, 5} := by
  unfold GnomonPascalCell
  rw [Nat.choose_eq_fast_choose]
  decide +kernel

set_option maxRecDepth 10000 in
-- Cast normalization of the certified finite products requires this recursion budget.
theorem consumer31_checked :
    gnomonPascalSmallCarryMass 31 + gnomonRepeatedCarryMass 31 +
      gnomonCofactorSemiprimeBudget 31 {2, 3, 5} + gnomonPascalShellHigherPrimePowerMass 31 <
        Real.log (GnomonPascalCell 31 : ℝ) := by
  have hp : (0 : ℝ) < (residualProduct 31 : ℝ) * (sieveProduct 31 {2, 3, 5} : ℝ) := by
    exact_mod_cast products31_checked.1
  have hc : (residualProduct 31 : ℝ) * (sieveProduct 31 {2, 3, 5} : ℝ) <
      (GnomonPascalCell 31 : ℝ) * (semiprimeProduct 31 {2, 3, 5} : ℝ) := by
    exact_mod_cast products31_checked.2
  have h := Real.log_lt_log hp hc
  have hr0 : (residualProduct 31 : ℝ) ≠ 0 := by exact_mod_cast (residual_pos 31).ne'
  have hv0 : (sieveProduct 31 {2, 3, 5} : ℝ) ≠ 0 := by exact_mod_cast (sieve_pos 31 {2, 3, 5}).ne'
  have hc0 : (GnomonPascalCell 31 : ℝ) ≠ 0 := by
    exact_mod_cast ((Nat.choose_pos (by norm_num : 62 ≤ 1023)) : 0 < GnomonPascalCell 31).ne'
  have hd0 : (semiprimeProduct 31 {2, 3, 5} : ℝ) ≠ 0 := by exact_mod_cast (semiprimeProduct_pos 31 {2, 3, 5}).ne'
  rw [Real.log_mul hr0 hv0, Real.log_mul hc0 hd0] at h
  have hR := residual_log_product 31
  have hV := sieve_log_product 31 {2, 3, 5}
  have hD := semiprime_log_product 31 {2, 3, 5}
  have hu := min_le_right (gnomonCofactorLeastFactorBudget 31 {2, 3, 5})
    (gnomonCofactorSieveMass 31 {2, 3, 5} - gnomonCofactorSemiprimeMass 31 {2, 3, 5})
  change gnomonCofactorSemiprimeBudget 31 {2, 3, 5} ≤ _ at hu
  linarith

/-- The recovered strict margin certifies a strict improvement over the failed 032 envelope. -/
theorem strict_gain31_checked : gnomonCofactorSemiprimeBudget 31 {2, 3, 5} <
    gnomonCofactorLeastFactorBudget 31 {2, 3, 5} := by
  have h := consumer31_checked
  have hf := DkMathTest.NumberTheory.GnomonCofactorLeastFactorCalibration.consumer_failure31_checked
  linarith

/-- Small equality rules out universal strict gain over every admissible anchor. -/
theorem equality3_checked : gnomonCofactorSemiprimeBudget 3 {2, 3, 5} =
    gnomonCofactorLeastFactorBudget 3 {2, 3, 5} := by
  have hd : gnomonCofactorSemiprimeMass 3 {2, 3, 5} = 0 := by
    rw [semiprime_log_product]
    have h : semiprimeProduct 3 {2, 3, 5} = 1 := by decide +kernel
    rw [h]
    norm_num
  unfold gnomonCofactorSemiprimeBudget
  rw [hd, sub_zero]
  exact min_eq_left ((gnomonCofactorLeastFactorBudget_le_sieveBudget _ _).trans (min_le_right _ _))

end DkMathTest.NumberTheory.GnomonCofactorSemiprimeCalibration
