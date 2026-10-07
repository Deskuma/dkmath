/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.GnomonCofactorSieve
import DkMathTest.NumberTheory.GnomonCofactorWindowCalibration

#print "file: DkMathTest.NumberTheory.GnomonCofactorSieveCalibration"

namespace DkMathTest.NumberTheory.GnomonCofactorSieveCalibration

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

private theorem envelope_log_min (n : ℕ) (S : Finset ℕ) :
    gnomonPascalSmallCarryMass n + gnomonRepeatedCarryMass n +
      gnomonCofactorSieveBudget n S + gnomonPascalShellHigherPrimePowerMass n =
    min (Real.log ((residualProduct n * geometricProduct n : ℕ) : ℝ))
      (Real.log ((residualProduct n * sieveProduct n S : ℕ) : ℝ)) := by
  unfold gnomonCofactorSieveBudget
  rw [geometric_log_product, sieve_log_product]
  have hR := residual_log_product n
  have hr0 : (residualProduct n : ℝ) ≠ 0 := by
    unfold residualProduct
    simp only [Nat.cast_mul]
    exact mul_ne_zero (mul_ne_zero (minFac_product_ne_zero _) (minFac_product_ne_zero _))
      (minFac_product_ne_zero _)
  have hg0 : (geometricProduct n : ℝ) ≠ 0 := by
    unfold geometricProduct
    rw [Nat.cast_ne_zero]
    apply Finset.prod_ne_zero_iff.mpr
    intro k _
    have hc := Nat.choose_pos (Nat.sub_le ((n ^ 2 + 2 * n) / k) (max (n ^ 2 / k) (2 * n)))
    have hp : 0 < max 1 ((n ^ 2 + 2 * n) / k) := lt_of_lt_of_le (by decide) (le_max_left _ _)
    exact (lt_min hc (pow_pos hp _)).ne'
  have hs0 : (sieveProduct n S : ℝ) ≠ 0 := by
    unfold sieveProduct
    rw [Nat.cast_ne_zero]
    apply Finset.prod_ne_zero_iff.mpr
    intro k _
    apply Finset.prod_ne_zero_iff.mpr
    intro q hq
    have h := Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1
    omega
  simp only [Nat.cast_mul]
  rw [Real.log_mul hr0 hg0, Real.log_mul hr0 hs0]
  by_cases h : Real.log (geometricProduct n : ℝ) ≤ Real.log (sieveProduct n S : ℝ)
  · have ha : Real.log (residualProduct n : ℝ) + Real.log (geometricProduct n : ℝ) ≤
        Real.log (residualProduct n : ℝ) + Real.log (sieveProduct n S : ℝ) := by linarith only [h]
    rw [min_eq_left h, min_eq_left ha]
    linarith only [hR]
  · have h' := le_of_not_ge h
    have ha : Real.log (residualProduct n : ℝ) + Real.log (sieveProduct n S : ℝ) ≤
        Real.log (residualProduct n : ℝ) + Real.log (geometricProduct n : ℝ) := by linarith only [h']
    rw [min_eq_right h', min_eq_right ha]
    linarith only [hR]

/-- The reused basis has the synchronization period 30. -/
theorem basis30_checked : IsFinitePrimeBasis ({2, 3, 5} : Finset ℕ) ∧
    finitePrimeBasisProduct ({2, 3, 5} : Finset ℕ) = 30 := by
  exact ⟨basis_prime, by decide +kernel⟩

/-- Equality at n=3 refutes a strict improvement at every admissible anchor. -/
theorem equality3_checked : gnomonCofactorSieveBudget 3 {2, 3, 5} =
    gnomonCofactorGeometricBudget 3 := by
  apply le_antisymm (gnomonCofactorSieveBudget_le_geometricBudget _ _)
  have h := gnomonCofactorWindowMass_le_sieveBudget (by omega : 3 ≤ 3)
    basis_prime (basis_bound (by omega : 3 ≤ 3))
  simpa only [basis,
    DkMathTest.NumberTheory.GnomonCofactorWindowCalibration.no_slack3_checked] using h

/-- The old composite-only obstruction is actually deleted. -/
theorem windows7_checked :
    gnomonCofactorSieveCandidates 7 2 {2, 3, 5} = {29, 31} ∧
    gnomonCofactorSieveCandidates 7 3 {2, 3, 5} = {17, 19} ∧
    gnomonCofactorSieveCandidates 7 4 {2, 3, 5} = ∅ := by decide +kernel

/-- No surviving composite occurs at any earlier admissible anchor. -/
theorem no_composites_before9_checked : ∀ n ∈ Finset.Icc 3 8,
    ∀ k ∈ Finset.Icc 2 (n - 1),
      (gnomonCofactorSieveCandidates n k {2, 3, 5}).filter (fun q => ¬ q.Prime) = ∅ := by
  decide +kernel

/-- The first error is log(49), not the carry weight log(7). -/
theorem composite_error9_checked :
    gnomonCofactorSieveCompositeError 9 {2, 3, 5} = Real.log 49 := by
  have h : ∀ k ∈ Finset.Icc 2 (9 - 1),
      (gnomonCofactorSieveCandidates 9 k {2, 3, 5}).filter (fun q => ¬ q.Prime) =
        if k = 2 then {49} else ∅ := by decide +kernel
  unfold gnomonCofactorSieveCompositeError
  calc
    _ = ∑ k ∈ Finset.Icc 2 (9 - 1), if k = 2 then Real.log 49 else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [h k hk]
      split_ifs <;> norm_num
    _ = _ := by norm_num

/-- Sieve candidates also include composites with two distinct prime bases. -/
theorem compound_composite12_checked :
    77 ∈ gnomonCofactorSieveCandidates 12 2 {2, 3, 5} ∧ ¬ IsPrimePow (77 : ℕ) := by
  decide +kernel

/-- Exact integer products at the corrected obstruction. -/
theorem products7_checked : sieveProduct 7 {2, 3, 5} = 290377 ∧
    geometricProduct 7 = 128290919715 ∧ residualProduct 7 = 675 ∧
    0 < residualProduct 7 * sieveProduct 7 {2, 3, 5} ∧
    residualProduct 7 * sieveProduct 7 {2, 3, 5} < GnomonPascalCell 7 := by
  decide +kernel

theorem strict_saving7_checked :
    gnomonCofactorSieveBudget 7 {2, 3, 5} < gnomonCofactorGeometricBudget 7 := by
  have h : gnomonCofactorSieveMass 7 {2, 3, 5} < gnomonCofactorGeometricBudget 7 := by
    rw [sieve_log_product, geometric_log_product, products7_checked.1, products7_checked.2.1]
    exact Real.log_lt_log (by norm_num) (by norm_num)
  exact (min_le_right _ _).trans_lt h

/-- The new consumer passes the anchor where the 030 consumer was refuted. -/
theorem consumer7_checked :
    gnomonPascalSmallCarryMass 7 + gnomonRepeatedCarryMass 7 +
      gnomonCofactorSieveBudget 7 {2, 3, 5} + gnomonPascalShellHigherPrimePowerMass 7 <
        Real.log (GnomonPascalCell 7 : ℝ) := by
  rw [envelope_log_min]
  apply (min_le_right _ _).trans_lt
  exact Real.log_lt_log (by exact_mod_cast products7_checked.2.2.2.1)
    (by exact_mod_cast products7_checked.2.2.2.2)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Full kernel evaluation of the 29 carry carriers and both integer products needs this budget.
/-- The fixed 30-wheel still fails, even with the cap, at anchor 29. -/
theorem products_failure29_checked :
    GnomonPascalCell 29 < residualProduct 29 * sieveProduct 29 {2, 3, 5} ∧
    GnomonPascalCell 29 < residualProduct 29 * geometricProduct 29 := by
  unfold GnomonPascalCell geometricProduct
  rw [Nat.choose_eq_fast_choose]
  decide +kernel

theorem consumer_failure29_checked : Real.log (GnomonPascalCell 29 : ℝ) <
    gnomonPascalSmallCarryMass 29 + gnomonRepeatedCarryMass 29 +
      gnomonCofactorSieveBudget 29 {2, 3, 5} + gnomonPascalShellHigherPrimePowerMass 29 := by
  rw [envelope_log_min]
  apply lt_min
  · exact Real.log_lt_log (by exact_mod_cast (Nat.choose_pos (by norm_num : 58 ≤ 899)))
      (by exact_mod_cast products_failure29_checked.2)
  · exact Real.log_lt_log (by exact_mod_cast (Nat.choose_pos (by norm_num : 58 ≤ 899)))
      (by exact_mod_cast products_failure29_checked.1)

/-- A period-average count without an endpoint correction is not an upper bound. -/
theorem density_only_fails3_checked :
    ((Finset.Icc 1 30).filter (fun q => Nat.Coprime q 30)).card * (7 - 6) <
      30 * (gnomonCofactorSieveCandidates 3 2 {2, 3, 5}).card := by decide +kernel

/-- A basis above the width may delete the very prime whose mass must be bounded. -/
theorem unsafe_basis3_checked :
    gnomonCofactorSieveCandidates 3 2 {7} = ∅ ∧
    gnomonCofactorWindowPrimes 3 2 = {7} := by decide +kernel

end DkMathTest.NumberTheory.GnomonCofactorSieveCalibration
