/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.GnomonCofactorWindow

#print "file: DkMathTest.NumberTheory.GnomonCofactorWindowCalibration"

namespace DkMathTest.NumberTheory.GnomonCofactorWindowCalibration

open DkMath.NumberTheory.Legendre
open scoped BigOperators

private def binomialProduct (n : ℕ) : ℕ :=
  ∏ k ∈ Finset.Icc 2 (n - 1), Nat.choose ((n ^ 2 + 2 * n) / k)
    ((n ^ 2 + 2 * n) / k - max (n ^ 2 / k) (2 * n))

private theorem budget_log_product (n : ℕ) :
    gnomonCofactorBinomialBudget n = Real.log (binomialProduct n : ℝ) := by
  unfold gnomonCofactorBinomialBudget binomialProduct
  rw [Nat.cast_prod, Real.log_prod]
  intro k _
  exact_mod_cast (Nat.choose_pos (Nat.sub_le _ _)).ne'

private def geometricProduct (n : ℕ) : ℕ :=
  ∏ k ∈ Finset.Icc 2 (n - 1), min
    (Nat.choose ((n ^ 2 + 2 * n) / k)
      ((n ^ 2 + 2 * n) / k - max (n ^ 2 / k) (2 * n)))
    ((max 1 ((n ^ 2 + 2 * n) / k)) ^
      ((((n ^ 2 + 2 * n) / k + 1) / 2) - ((max (n ^ 2 / k) (2 * n) + 1) / 2)))

private theorem geometric_log_product (n : ℕ) :
    gnomonCofactorGeometricBudget n = Real.log (geometricProduct n : ℝ) := by
  unfold gnomonCofactorGeometricBudget geometricProduct
  rw [Nat.cast_prod, Real.log_prod]
  intro k _
  have hc := Nat.choose_pos (Nat.sub_le ((n ^ 2 + 2 * n) / k) (max (n ^ 2 / k) (2 * n)))
  have hp : 0 < max 1 ((n ^ 2 + 2 * n) / k) := lt_of_lt_of_le (by decide) (le_max_left _ _)
  exact_mod_cast (lt_min hc (pow_pos hp _)).ne'

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

private def residualProduct (n : ℕ) : ℕ :=
  (∏ d ∈ gnomonPascalSmallCarryEvents n, d.minFac) *
  (∏ d ∈ (gnomonPascalLargeCarryEvents n).filter (fun d => ¬ d.Prime), d.minFac) *
  (∏ d ∈ shellHigherPrimePowerEvents n, d.minFac)

private theorem minFac_product_ne_zero (s : Finset ℕ) :
    ((∏ d ∈ s, d.minFac : ℕ) : ℝ) ≠ 0 := by
  have h : 0 < ∏ d ∈ s, d.minFac := Finset.prod_pos (fun d _ => Nat.minFac_pos d)
  exact_mod_cast h.ne'

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

private theorem envelope_log_product (n : ℕ) :
    gnomonPascalSmallCarryMass n + gnomonRepeatedCarryMass n +
      gnomonCofactorGeometricBudget n + gnomonPascalShellHigherPrimePowerMass n =
        Real.log ((residualProduct n * geometricProduct n : ℕ) : ℝ) := by
  have hr := residual_log_product n
  have hU := geometric_log_product n
  rw [Nat.cast_mul, Real.log_mul, ← hr, ← hU]
  · ring
  · unfold residualProduct
    simp only [Nat.cast_mul]
    exact mul_ne_zero (mul_ne_zero (minFac_product_ne_zero _) (minFac_product_ne_zero _))
      (minFac_product_ne_zero _)
  · unfold geometricProduct
    rw [Nat.cast_ne_zero]
    apply Finset.prod_ne_zero_iff.mpr
    intro k _
    have hc := Nat.choose_pos (Nat.sub_le ((n ^ 2 + 2 * n) / k) (max (n ^ 2 / k) (2 * n)))
    have hp : 0 < max 1 ((n ^ 2 + 2 * n) / k) := lt_of_lt_of_le (by decide) (le_max_left _ _)
    exact (lt_min hc (pow_pos hp _)).ne'

/-- The first cofactor window is exactly the old singleton prime 7. -/
theorem window3_checked : gnomonCofactorWindowPrimes 3 2 = {7} := by decide +kernel

/-- At the only earlier admissible anchor the independent envelope is exact. -/
theorem no_slack3_checked : gnomonCofactorWindowMass 3 = gnomonCofactorGeometricBudget 3 := by
  rw [gnomonCofactorWindowMass_eq_singleton (by omega), gnomonSingletonCarryMass,
    geometric_log_product]
  have hc : (gnomonPascalLargeCarryEvents 3).filter Nat.Prime = {7} := by decide +kernel
  have hU : geometricProduct 3 = 7 := by decide +kernel
  rw [hc, hU, Finset.sum_singleton, ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]

/-- All three nonempty numerical windows at the first failure anchor. -/
theorem windows7_checked :
    gnomonCofactorWindowPrimes 7 2 = {29, 31} ∧
    gnomonCofactorWindowPrimes 7 3 = {17, 19} ∧
    gnomonCofactorWindowPrimes 7 4 = ∅ := by decide +kernel

/-- The independent coefficient charges the composite-only window (14,15]. -/
theorem composite_window7_checked :
    Nat.choose ((7 ^ 2 + 2 * 7) / 4)
      ((7 ^ 2 + 2 * 7) / 4 - max (7 ^ 2 / 4) (2 * 7)) = 15 := by decide +kernel

/-- Singleton and repeated labels are different sectors, even at small anchors. -/
theorem carry_parts7_checked :
    gnomonPascalSmallCarryEvents 7 = {3, 5, 9} ∧
    (gnomonPascalLargeCarryEvents 7).filter (fun d => ¬ d.Prime) = {25, 27} ∧
    (gnomonPascalLargeCarryEvents 7).filter Nat.Prime = {17, 19, 29, 31} ∧
    shellHigherPrimePowerEvents 7 = ∅ := by decide +kernel

theorem singleton4_checked : gnomonCofactorWindowMass 4 = Real.log 11 := by
  rw [gnomonCofactorWindowMass_eq_singleton (by omega), gnomonSingletonCarryMass]
  have hc : (gnomonPascalLargeCarryEvents 4).filter Nat.Prime = {11} := by decide +kernel
  rw [hc, Finset.sum_singleton, ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
  norm_num

theorem binomial4_checked : gnomonCofactorBinomialBudget 4 = Real.log 495 := by
  rw [budget_log_product]
  have hc : binomialProduct 4 = 495 := by decide +kernel
  rw [hc]
  norm_num

theorem geometric4_checked : gnomonCofactorGeometricBudget 4 = Real.log 144 := by
  rw [geometric_log_product]
  have hc : geometricProduct 4 = 144 := by decide +kernel
  rw [hc]
  norm_num

/-- The first strict slack is a symbolic log comparison, not a floating test. -/
theorem strict_slack4_checked : gnomonCofactorWindowMass 4 < gnomonCofactorGeometricBudget 4 := by
  rw [singleton4_checked, geometric4_checked]
  exact Real.log_lt_log (by norm_num) (by norm_num)

/-- Complete integer evaluation underlying the first failed consumer. -/
theorem integer_failure7_checked :
    binomialProduct 7 = 802638325125 ∧ geometricProduct 7 = 128290919715 ∧ residualProduct 7 = 675 ∧
    GnomonPascalCell 7 = 37387265592825 ∧
    GnomonPascalCell 7 < residualProduct 7 * geometricProduct 7 := by decide +kernel

/-- The universal strict-consumer claim fails already at n=7. -/
theorem consumer_failure7_checked :
    Real.log (GnomonPascalCell 7 : ℝ) <
      gnomonPascalSmallCarryMass 7 + gnomonRepeatedCarryMass 7 +
      gnomonCofactorGeometricBudget 7 + gnomonPascalShellHigherPrimePowerMass 7 := by
  rw [envelope_log_product]
  apply Real.log_lt_log
  · exact_mod_cast (Nat.choose_pos (by norm_num : 2 * 7 ≤ 7 ^ 2 + 2 * 7))
  · exact_mod_cast integer_failure7_checked.2.2.2.2

/-- Earlier admissible anchors satisfy this exact-higher consumer, so 7 is first. -/
theorem consumer_before7_checked (n : ℕ) (hn : 3 ≤ n) (hn7 : n < 7) :
    gnomonPascalSmallCarryMass n + gnomonRepeatedCarryMass n +
      gnomonCofactorGeometricBudget n + gnomonPascalShellHigherPrimePowerMass n <
        Real.log (GnomonPascalCell n : ℝ) := by
  have hi : ∀ n ∈ Finset.Icc 3 6,
      0 < residualProduct n * geometricProduct n ∧
      residualProduct n * geometricProduct n < GnomonPascalCell n := by decide +kernel
  have h := hi n (Finset.mem_Icc.mpr ⟨hn, by omega⟩)
  rw [envelope_log_product]
  exact Real.log_lt_log (by exact_mod_cast h.1) (by exact_mod_cast h.2)

/-- Parity supplies a passing anchor that the binomial-only estimate loses. -/
theorem consumer8_checked :
    gnomonPascalSmallCarryMass 8 + gnomonRepeatedCarryMass 8 +
      gnomonCofactorGeometricBudget 8 + gnomonPascalShellHigherPrimePowerMass 8 <
        Real.log (GnomonPascalCell 8 : ℝ) := by
  have hi : 0 < residualProduct 8 * geometricProduct 8 ∧
      residualProduct 8 * geometricProduct 8 < GnomonPascalCell 8 := by decide +kernel
  rw [envelope_log_product]
  exact Real.log_lt_log (by exact_mod_cast hi.1) (by exact_mod_cast hi.2)

end DkMathTest.NumberTheory.GnomonCofactorWindowCalibration
