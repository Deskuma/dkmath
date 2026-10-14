/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.GnomonCentralCarryCompensation

#print "file: DkMath.NumberTheory.Legendre.GnomonPooledThresholdAudit"

namespace DkMath.NumberTheory.Legendre
open scoped BigOperators

/-- Pool every repeated prime-base contribution above an independently specified threshold. -/
def gnomonResidualThresholdProduct (S : Finset ℕ) (t : ℕ) : ℕ :=
  ∏ d ∈ S.filter (fun d => t ≤ d.minFac), d.minFac

/-- A canonical threshold-capacity principle. This sufficient principle is refuted below. -/
def gnomonThresholdPooledCompensation (n : ℕ) : Prop :=
  ∀ t ∈ Finset.Icc 2 (2 * n),
    gnomonResidualThresholdProduct (gnomonSmallOnlyCarryEvents n) t ≤
      gnomonResidualThresholdProduct (gnomonCentralOnlyCarryEvents n) t

/-- Each base contribution is retained once, including repeated exponent coordinates. -/
theorem gnomonResidualThresholdProduct_split (S : Finset ℕ) (t : ℕ) :
    (∏ d ∈ S, d.minFac) = gnomonResidualThresholdProduct S t *
      ∏ d ∈ S.filter (fun d => d.minFac < t), d.minFac := by
  unfold gnomonResidualThresholdProduct
  simpa only [not_le] using
    (Finset.prod_filter_mul_prod_filter_not S (fun d => t ≤ d.minFac)
      (fun d => d.minFac)).symm

/-- The lowest threshold recovers the full prime-base product. -/
theorem gnomonResidualThresholdProduct_two {S : Finset ℕ}
    (hS : ∀ d ∈ S, IsPrimePow d) :
    gnomonResidualThresholdProduct S 2 = ∏ d ∈ S, d.minFac := by
  have he : S.filter (fun d => 2 ≤ d.minFac) = S := by
    apply Finset.filter_eq_self.mpr
    intro d hd
    exact (Nat.minFac_prime (hS d hd).ne_one).two_le
  unfold gnomonResidualThresholdProduct
  rw [he]

/-- Logical sufficiency only: no uniform threshold-capacity hypothesis is asserted. -/
theorem gnomonSmallCarry_le_central_of_thresholdPooling {n : ℕ} (hn : 3 ≤ n)
    (hpool : gnomonThresholdPooledCompensation n) :
    gnomonPascalSmallCarryMass n ≤ Real.log (Nat.choose (2 * n) n : ℝ) := by
  apply (gnomonCarry_compensation_iff_product n).mpr
  have h := hpool 2 (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
  rw [gnomonResidualThresholdProduct_two (by
      intro d hd
      exact (mem_gnomonPascalLowCarryEvents.mp
        (Finset.mem_filter.mp (Finset.mem_sdiff.mp hd).1).1).2.2.1),
    gnomonResidualThresholdProduct_two (by
      intro d hd
      exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hd).1).2.1)] at h
  exact h

/-- Pooled high-base capacity fails although the full residual-product comparison holds. -/
theorem gnomonThresholdPooledCompensation_fails27 : ¬ gnomonThresholdPooledCompensation 27 := by
  intro hpool
  have h := hpool 8 (by decide)
  have hl : gnomonResidualThresholdProduct (gnomonSmallOnlyCarryEvents 27) 8 = 4807 := by
    decide +kernel
  have hr : gnomonResidualThresholdProduct (gnomonCentralOnlyCarryEvents 27) 8 = 2491 := by
    decide +kernel
  rw [hl, hr] at h
  omega

end DkMath.NumberTheory.Legendre
