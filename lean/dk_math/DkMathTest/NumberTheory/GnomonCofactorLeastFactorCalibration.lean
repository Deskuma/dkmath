/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.GnomonCofactorLeastFactor
import DkMathTest.NumberTheory.GnomonCofactorSieveCalibration

#print "file: DkMathTest.NumberTheory.GnomonCofactorLeastFactorCalibration"

namespace DkMathTest.NumberTheory.GnomonCofactorLeastFactorCalibration

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

private def squareProduct (n : ℕ) (S : Finset ℕ) : ℕ :=
  ∏ k ∈ Finset.Icc 2 (n - 1), ∏ q ∈ gnomonCofactorSquareWitnesses n k S, q

private theorem squareProduct_pos (n : ℕ) (S : Finset ℕ) : 0 < squareProduct n S := by
  apply Finset.prod_pos
  intro k _
  apply Finset.prod_pos
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
  have h := (gnomonCofactorFactorPairs_product_mem (Finset.mem_filter.mp hp).1).1
  have hlo := (Finset.mem_Icc.mp (Finset.mem_filter.mp h).1).1
  omega

private theorem square_log_product (n : ℕ) (S : Finset ℕ) :
    gnomonCofactorSquareWitnessMass n S = Real.log (squareProduct n S : ℝ) := by
  unfold gnomonCofactorSquareWitnessMass squareProduct
  rw [Nat.cast_prod, Real.log_prod]
  · apply Finset.sum_congr rfl
    intro k _
    rw [Nat.cast_prod, Real.log_prod]
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    have h := (gnomonCofactorFactorPairs_product_mem (Finset.mem_filter.mp hp).1).1
    have hlo := (Finset.mem_Icc.mp (Finset.mem_filter.mp h).1).1
    exact_mod_cast (show p.1 * p.2 ≠ 0 by omega)
  · intro k _
    rw [Nat.cast_ne_zero]
    apply Finset.prod_ne_zero_iff.mpr
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    have h := (gnomonCofactorFactorPairs_product_mem (Finset.mem_filter.mp hp).1).1
    have hlo := (Finset.mem_Icc.mp (Finset.mem_filter.mp h).1).1
    omega

/-- 49 is routed structurally by its canonical least factor and complement. -/
theorem normal9_checked : (49 : ℕ).minFac = 7 ∧ 49 / (49 : ℕ).minFac = 7 ∧
    (7, 7) ∈ gnomonCofactorFactorPairs 9 2 {2, 3, 5} := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  convert gnomonCofactorSieveComposite_mem_factorPairs
    (by decide +kernel : 49 ∈ gnomonCofactorSieveCandidates 9 2 {2, 3, 5})
    (by decide +kernel : ¬ Nat.Prime 49) using 1
  decide +kernel

/-- 77 routes to (7,11), rather than to a prime-square diagonal. -/
theorem normal12_checked : (77 : ℕ).minFac = 7 ∧ 77 / (77 : ℕ).minFac = 11 ∧
    (7, 11) ∈ gnomonCofactorFactorPairs 12 2 {2, 3, 5} ∧
    77 ∉ gnomonCofactorSquareWitnesses 12 2 {2, 3, 5} := by
  refine ⟨by decide +kernel, by decide +kernel, ?_, by decide +kernel⟩
  convert gnomonCofactorSieveComposite_mem_factorPairs
    (by decide +kernel : 77 ∈ gnomonCofactorSieveCandidates 12 2 {2, 3, 5})
    (by decide +kernel : ¬ Nat.Prime 77) using 1
  decide +kernel

/-- Complete canonical fibers at the retained 031 failure. -/
theorem canonical29_checked : ∀ k ∈ Finset.Icc 2 28,
    ((gnomonCofactorSieveCandidates 29 k {2, 3, 5}).filter (fun q => ¬ q.Prime)).image
      (fun q => (q, q.minFac, q / q.minFac)) =
    if k = 2 then {(427, 7, 61), (437, 19, 23)} else
    if k = 3 then {(287, 7, 41), (289, 17, 17), (299, 13, 23)} else
    if k = 4 then {(217, 7, 31), (221, 13, 17)} else
    if k = 5 then {(169, 13, 13)} else
    if k = 6 then {(143, 11, 13)} else
    if k = 7 then {(121, 11, 11)} else
    if k = 11 then {(77, 7, 11)} else ∅ := by decide +kernel

/-- A noninitial basis only excludes its members; 3 can be below its maximum 5. -/
theorem noninitial_basis_checked :
    9 ∈ gnomonCofactorSieveCandidates 4 2 {2, 5} ∧ (9 : ℕ).minFac = 3 := by
  decide +kernel

/-- The cover is genuinely larger than the canonical indexing. -/
theorem duplicate32_checked :
    (7, 77) ∈ gnomonCofactorFactorPairs 32 2 {2, 3, 5} ∧
    (11, 49) ∈ gnomonCofactorFactorPairs 32 2 {2, 3, 5} ∧
    7 * 77 = 539 ∧ 11 * 49 = 539 ∧ (539 : ℕ).minFac = 7 := by decide +kernel

/-- At the first surviving composite the full cover has exactly one pair. -/
theorem pairs9_checked : ∀ k ∈ Finset.Icc 2 8,
    gnomonCofactorFactorPairs 9 k {2, 3, 5} = if k = 2 then {(7, 7)} else ∅ := by
  decide +kernel

theorem error_bound9_checked : gnomonCofactorFactorPairBudget 9 {2, 3, 5} = Real.log 49 := by
  unfold gnomonCofactorFactorPairBudget
  calc
    _ = ∑ k ∈ Finset.Icc 2 8, if k = 2 then Real.log 49 else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [pairs9_checked k hk]
      split_ifs <;> norm_num
    _ = _ := by norm_num

/-- The diagonal lower witness removes exactly log(49) at n=9. -/
theorem square_error9_checked : gnomonCofactorSquareWitnessMass 9 {2, 3, 5} = Real.log 49 := by
  rw [square_log_product]
  have h : squareProduct 9 {2, 3, 5} = 49 := by decide +kernel
  rw [h]
  norm_num

theorem corrected9_exact_checked : gnomonCofactorLeastFactorBudget 9 {2, 3, 5} =
    gnomonCofactorWindowMass 9 := by
  apply le_antisymm
  · have he := gnomonCofactorSieveMass_eq_window_add_error basis_prime
      (basis_bound (by omega : 3 ≤ 9))
    simp only [basis, DkMathTest.NumberTheory.GnomonCofactorSieveCalibration.composite_error9_checked] at he
    unfold gnomonCofactorLeastFactorBudget
    rw [square_error9_checked]
    have h := min_le_right (gnomonCofactorSieveBudget 9 {2, 3, 5})
      (gnomonCofactorSieveMass 9 {2, 3, 5} - Real.log 49)
    linarith
  · exact gnomonCofactorWindowMass_le_leastFactorBudget (by omega) basis_prime
      (basis_bound (by omega))

/-- The earlier n=7 recovery is preserved by the corrected envelope. -/
theorem consumer7_checked :
    gnomonPascalSmallCarryMass 7 + gnomonRepeatedCarryMass 7 +
      gnomonCofactorLeastFactorBudget 7 {2, 3, 5} + gnomonPascalShellHigherPrimePowerMass 7 <
        Real.log (GnomonPascalCell 7 : ℝ) := by
  have h := DkMathTest.NumberTheory.GnomonCofactorSieveCalibration.consumer7_checked
  have hu := gnomonCofactorLeastFactorBudget_le_sieveBudget 7 {2, 3, 5}
  linarith

/-- There is no universal strict improvement over 031: equality occurs at n=3. -/
theorem equality3_checked : gnomonCofactorLeastFactorBudget 3 {2, 3, 5} =
    gnomonCofactorSieveBudget 3 {2, 3, 5} := by
  unfold gnomonCofactorLeastFactorBudget
  have hl : gnomonCofactorSquareWitnessMass 3 {2, 3, 5} = 0 := by
    rw [square_log_product]
    have h : squareProduct 3 {2, 3, 5} = 1 := by decide +kernel
    rw [h]
    norm_num
  rw [hl, sub_zero]
  exact min_eq_left (min_le_right _ _)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Exact carry products and the binomial cell at 29 require this finite kernel budget.
theorem products29_checked : squareProduct 29 {2, 3, 5} = 289 * 169 * 121 ∧
    0 < residualProduct 29 * sieveProduct 29 {2, 3, 5} ∧
    residualProduct 29 * sieveProduct 29 {2, 3, 5} <
      GnomonPascalCell 29 * squareProduct 29 {2, 3, 5} := by
  unfold GnomonPascalCell
  rw [Nat.choose_eq_fast_choose]
  decide +kernel

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

set_option maxRecDepth 10000 in
-- Cast normalization of the large certified 29 products needs this recursion budget.
/-- A concrete strict improvement over the failed 031 consumer, using lower square mass. -/
theorem consumer29_checked :
    gnomonPascalSmallCarryMass 29 + gnomonRepeatedCarryMass 29 +
      gnomonCofactorLeastFactorBudget 29 {2, 3, 5} + gnomonPascalShellHigherPrimePowerMass 29 <
        Real.log (GnomonPascalCell 29 : ℝ) := by
  have hp : (0 : ℝ) < (residualProduct 29 : ℝ) * (sieveProduct 29 {2, 3, 5} : ℝ) := by
    exact_mod_cast products29_checked.2.1
  have hc : (residualProduct 29 : ℝ) * (sieveProduct 29 {2, 3, 5} : ℝ) <
      (GnomonPascalCell 29 : ℝ) * (squareProduct 29 {2, 3, 5} : ℝ) := by
    exact_mod_cast products29_checked.2.2
  have h := Real.log_lt_log hp hc
  have hr0 : (residualProduct 29 : ℝ) ≠ 0 := by exact_mod_cast (residual_pos 29).ne'
  have hv0 : (sieveProduct 29 {2, 3, 5} : ℝ) ≠ 0 := by exact_mod_cast (sieve_pos 29 {2, 3, 5}).ne'
  have hc0 : (GnomonPascalCell 29 : ℝ) ≠ 0 := by
    exact_mod_cast ((Nat.choose_pos (by norm_num : 58 ≤ 899)) : 0 < GnomonPascalCell 29).ne'
  have hl0 : (squareProduct 29 {2, 3, 5} : ℝ) ≠ 0 := by exact_mod_cast (squareProduct_pos 29 {2, 3, 5}).ne'
  rw [Real.log_mul hr0 hv0, Real.log_mul hc0 hl0] at h
  have hR := residual_log_product 29
  have hV := sieve_log_product 29 {2, 3, 5}
  have hL := square_log_product 29 {2, 3, 5}
  have hu := min_le_right (gnomonCofactorSieveBudget 29 {2, 3, 5})
    (gnomonCofactorSieveMass 29 {2, 3, 5} - gnomonCofactorSquareWitnessMass 29 {2, 3, 5})
  change gnomonCofactorLeastFactorBudget 29 {2, 3, 5} ≤ _ at hu
  linarith

private theorem corrected_envelope_log_min (n : ℕ) (S : Finset ℕ) :
    gnomonPascalSmallCarryMass n + gnomonRepeatedCarryMass n +
      gnomonCofactorLeastFactorBudget n S + gnomonPascalShellHigherPrimePowerMass n =
    min (Real.log ((residualProduct n * geometricProduct n : ℕ) : ℝ))
      (Real.log ((residualProduct n * sieveProduct n S : ℕ) : ℝ) -
        Real.log (squareProduct n S : ℝ)) := by
  have hL : 0 ≤ gnomonCofactorSquareWitnessMass n S := by
    rw [square_log_product]
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ squareProduct n S by have := squareProduct_pos n S; omega)
  have hu : gnomonCofactorLeastFactorBudget n S =
      min (gnomonCofactorGeometricBudget n)
        (gnomonCofactorSieveMass n S - gnomonCofactorSquareWitnessMass n S) := by
    unfold gnomonCofactorLeastFactorBudget gnomonCofactorSieveBudget
    have hv : gnomonCofactorSieveMass n S - gnomonCofactorSquareWitnessMass n S ≤
        gnomonCofactorSieveMass n S := by linarith only [hL]
    rw [min_assoc, min_eq_right hv]
  have hr0 : (residualProduct n : ℝ) ≠ 0 := by exact_mod_cast (residual_pos n).ne'
  have hv0 : (sieveProduct n S : ℝ) ≠ 0 := by exact_mod_cast (sieve_pos n S).ne'
  have hg0 : (geometricProduct n : ℝ) ≠ 0 := by
    unfold geometricProduct
    rw [Nat.cast_ne_zero]
    apply Finset.prod_ne_zero_iff.mpr
    intro k _
    have hc := Nat.choose_pos (Nat.sub_le ((n ^ 2 + 2 * n) / k) (max (n ^ 2 / k) (2 * n)))
    have hp : 0 < max 1 ((n ^ 2 + 2 * n) / k) := lt_of_lt_of_le (by decide) (le_max_left _ _)
    exact (lt_min hc (pow_pos hp _)).ne'
  rw [hu, geometric_log_product, sieve_log_product, square_log_product]
  simp only [Nat.cast_mul]
  rw [Real.log_mul hr0 hg0, Real.log_mul hr0 hv0]
  have hR := residual_log_product n
  by_cases h : Real.log (geometricProduct n : ℝ) ≤
      Real.log (sieveProduct n S : ℝ) - Real.log (squareProduct n S : ℝ)
  · have ha : Real.log (residualProduct n : ℝ) + Real.log (geometricProduct n : ℝ) ≤
        Real.log (residualProduct n : ℝ) + Real.log (sieveProduct n S : ℝ) -
          Real.log (squareProduct n S : ℝ) := by linarith only [h]
    rw [min_eq_left h, min_eq_left ha]
    linarith only [hR]
  · have h' := le_of_not_ge h
    have ha : Real.log (residualProduct n : ℝ) + Real.log (sieveProduct n S : ℝ) -
        Real.log (squareProduct n S : ℝ) ≤
        Real.log (residualProduct n : ℝ) + Real.log (geometricProduct n : ℝ) := by
      linarith only [h']
    rw [min_eq_right h', min_eq_right ha]
    linarith only [hR]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Kernel evaluation of the 31 carry products and fast binomial cell needs this budget.
theorem products_failure31_checked :
    GnomonPascalCell 31 * squareProduct 31 {2, 3, 5} <
      residualProduct 31 * sieveProduct 31 {2, 3, 5} ∧
    GnomonPascalCell 31 < residualProduct 31 * geometricProduct 31 := by
  unfold GnomonPascalCell geometricProduct
  rw [Nat.choose_eq_fast_choose]
  decide +kernel

set_option maxRecDepth 10000 in
-- Cast normalization of the certified 31 products requires the same recursion budget.
/-- Square deletion still has a kernel-certified failure, with nonsquare composites remaining. -/
theorem consumer_failure31_checked : Real.log (GnomonPascalCell 31 : ℝ) <
    gnomonPascalSmallCarryMass 31 + gnomonRepeatedCarryMass 31 +
      gnomonCofactorLeastFactorBudget 31 {2, 3, 5} + gnomonPascalShellHigherPrimePowerMass 31 := by
  rw [corrected_envelope_log_min]
  apply lt_min
  · exact Real.log_lt_log (by exact_mod_cast (Nat.choose_pos (by norm_num : 62 ≤ 1023)))
      (by exact_mod_cast products_failure31_checked.2)
  · have hp : (0 : ℝ) < (GnomonPascalCell 31 : ℝ) * (squareProduct 31 {2, 3, 5} : ℝ) := by
      exact_mod_cast Nat.mul_pos
        ((Nat.choose_pos (by norm_num : 62 ≤ 1023)) : 0 < GnomonPascalCell 31)
        (squareProduct_pos 31 {2, 3, 5})
    have hc : (GnomonPascalCell 31 : ℝ) * (squareProduct 31 {2, 3, 5} : ℝ) <
        (residualProduct 31 : ℝ) * (sieveProduct 31 {2, 3, 5} : ℝ) := by
      exact_mod_cast products_failure31_checked.1
    have h := Real.log_lt_log hp hc
    have hc0 : (GnomonPascalCell 31 : ℝ) ≠ 0 := by
      exact_mod_cast ((Nat.choose_pos (by norm_num : 62 ≤ 1023)) : 0 < GnomonPascalCell 31).ne'
    have hl0 : (squareProduct 31 {2, 3, 5} : ℝ) ≠ 0 := by exact_mod_cast (squareProduct_pos 31 {2, 3, 5}).ne'
    rw [Real.log_mul hc0 hl0] at h
    simp only [Nat.cast_mul]
    linarith

end DkMathTest.NumberTheory.GnomonCofactorLeastFactorCalibration
