/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.GnomonCofactorLeastFactor

#print "file: DkMath.NumberTheory.Legendre.GnomonCofactorSemiprime"

/-! Distinct ordered prime products certify deletable composite mass. -/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.PrimorialUniverse
open scoped BigOperators

/-- Endpoint pairs with two prime factors, including the diagonal. -/
def gnomonCofactorSemiprimePairs (n k : ℕ) (S : Finset ℕ) : Finset (ℕ × ℕ) :=
  (gnomonCofactorFactorPairs n k S).filter (fun p => p.2.Prime)

private theorem pair_facts {n k : ℕ} {S : Finset ℕ} {p : ℕ × ℕ}
    (hp : p ∈ gnomonCofactorSemiprimePairs n k S) :
    p.1.Prime ∧ p.2.Prime ∧ p.1 ≤ p.2 := by
  obtain ⟨hc, hs⟩ := Finset.mem_filter.mp hp
  obtain ⟨r, hr, hm⟩ := Finset.mem_biUnion.mp hc
  obtain ⟨m, hmI, he⟩ := Finset.mem_image.mp hm
  subst p
  exact ⟨(Finset.mem_filter.mp hr).2.1, hs,
    (le_max_left _ _).trans (Finset.mem_Icc.mp (Finset.mem_filter.mp hmI).1).1⟩

/-- Unique factorization with ordered prime factors prevents product collisions. -/
theorem gnomonCofactorSemiprime_product_injective {n k : ℕ} {S : Finset ℕ} :
    Set.InjOn (fun p : ℕ × ℕ => p.1 * p.2) (↑(gnomonCofactorSemiprimePairs n k S)) := by
  intro a ha b hb he
  obtain ⟨haP, _, haO⟩ := pair_facts ha
  obtain ⟨hbP, hbQ, hbO⟩ := pair_facts hb
  change a.1 * a.2 = b.1 * b.2 at he
  have hd : a.1 ∣ b.1 * b.2 := he ▸ dvd_mul_right a.1 a.2
  rcases haP.dvd_mul.mp hd with hd | hd
  · have h1 : a.1 = b.1 := ((hbP.dvd_iff_eq haP.ne_one).mp hd).symm
    have h2 : a.2 = b.2 := Nat.eq_of_mul_eq_mul_left haP.pos (by simpa only [← h1] using he)
    exact Prod.ext h1 h2
  · have h1 : a.1 = b.2 := ((hbQ.dvd_iff_eq haP.ne_one).mp hd).symm
    have h2 : a.2 = b.1 := Nat.eq_of_mul_eq_mul_left haP.pos
      (by simpa only [← h1, Nat.mul_comm b.1 a.1] using he)
    have h3 : a.1 = b.1 := by omega
    exact Prod.ext h3 (by omega)

/-- Certainly-composite products, defined without a target composite or carry filter. -/
def gnomonCofactorSemiprimeWitnesses (n k : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (gnomonCofactorSemiprimePairs n k S).image (fun p => p.1 * p.2)

noncomputable def gnomonCofactorSemiprimeMass (n : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 (n - 1), ∑ q ∈ gnomonCofactorSemiprimeWitnesses n k S,
    Real.log (q : ℝ)

/-- The pair-weight sum is safe here precisely because its product map is injective. -/
theorem gnomonCofactorSemiprimeMass_eq_pair_sum (n : ℕ) (S : Finset ℕ) :
    gnomonCofactorSemiprimeMass n S =
      ∑ k ∈ Finset.Icc 2 (n - 1), ∑ p ∈ gnomonCofactorSemiprimePairs n k S,
        Real.log ((p.1 * p.2 : ℕ) : ℝ) := by
  apply Finset.sum_congr rfl
  intro k _
  exact Finset.sum_image gnomonCofactorSemiprime_product_injective

/-- All witnesses occur in the actual surviving composite carrier. -/
theorem gnomonCofactorSemiprimeWitnesses_subset_error (n k : ℕ) (S : Finset ℕ) :
    gnomonCofactorSemiprimeWitnesses n k S ⊆
      (gnomonCofactorSieveCandidates n k S).filter (fun q => ¬ q.Prime) := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨hc, hn⟩ := gnomonCofactorFactorPairs_product_mem (Finset.mem_filter.mp hp).1
  exact Finset.mem_filter.mpr ⟨hc, hn⟩

theorem gnomonCofactorSemiprimeMass_le_error (n : ℕ) (S : Finset ℕ) :
    gnomonCofactorSemiprimeMass n S ≤ gnomonCofactorSieveCompositeError n S := by
  apply Finset.sum_le_sum
  intro k _
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (gnomonCofactorSemiprimeWitnesses_subset_error n k S) (fun q hq _ => by
      have h := Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
      exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega)))

/-- Squares are included once, without adding their mass a second time. -/
theorem gnomonCofactorSquareWitnesses_subset_semiprime (n k : ℕ) (S : Finset ℕ) :
    gnomonCofactorSquareWitnesses n k S ⊆ gnomonCofactorSemiprimeWitnesses n k S := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨hc, he⟩ := Finset.mem_filter.mp hp
  have hrP : p.1.Prime := by
    obtain ⟨r, hr, hm⟩ := Finset.mem_biUnion.mp hc
    obtain ⟨m, _, heq⟩ := Finset.mem_image.mp hm
    subst p
    exact (Finset.mem_filter.mp hr).2.1
  exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hc, he ▸ hrP⟩, rfl⟩

theorem gnomonCofactorSquareWitnessMass_le_semiprimeMass (n : ℕ) (S : Finset ℕ) :
    gnomonCofactorSquareWitnessMass n S ≤ gnomonCofactorSemiprimeMass n S := by
  apply Finset.sum_le_sum
  intro k _
  apply Finset.sum_le_sum_of_subset_of_nonneg (gnomonCofactorSquareWitnesses_subset_semiprime n k S)
  intro q hq _
  have hc := gnomonCofactorSemiprimeWitnesses_subset_error n k S hq
  have h := Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).1
  exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))

/-- One corrected envelope, capped by the entire 032 envelope. -/
noncomputable def gnomonCofactorSemiprimeBudget (n : ℕ) (S : Finset ℕ) : ℝ :=
  min (gnomonCofactorLeastFactorBudget n S)
    (gnomonCofactorSieveMass n S - gnomonCofactorSemiprimeMass n S)

theorem gnomonCofactorWindowMass_le_semiprimeBudget {n : ℕ} {S : Finset ℕ}
    (hn : 3 ≤ n) (hS : IsFinitePrimeBasis S) (hbound : ∀ q ∈ S, q ≤ 2 * n) :
    gnomonCofactorWindowMass n ≤ gnomonCofactorSemiprimeBudget n S := by
  apply le_min (gnomonCofactorWindowMass_le_leastFactorBudget hn hS hbound)
  have he := gnomonCofactorSieveMass_eq_window_add_error hS hbound
  have hd := gnomonCofactorSemiprimeMass_le_error n S
  linarith

theorem gnomonCofactorSemiprimeBudget_le_leastFactorBudget (n : ℕ) (S : Finset ℕ) :
    gnomonCofactorSemiprimeBudget n S ≤ gnomonCofactorLeastFactorBudget n S := min_le_left _ _

theorem gnomonCofactorSemiprimeBudget_excess {n : ℕ} {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S) (hbound : ∀ q ∈ S, q ≤ 2 * n) :
    gnomonCofactorSemiprimeBudget n S - gnomonCofactorWindowMass n =
      min (gnomonCofactorLeastFactorBudget n S - gnomonCofactorWindowMass n)
        (gnomonCofactorSieveCompositeError n S - gnomonCofactorSemiprimeMass n S) := by
  unfold gnomonCofactorSemiprimeBudget
  rw [gnomonCofactorSieveMass_eq_window_add_error hS hbound, ← min_sub_sub_right]
  congr 1
  ring

theorem gnomonPascalOldLogBudget_semiprime_excess {n : ℕ} (hn : 3 ≤ n) (S : Finset ℕ) :
    gnomonPascalSmallCarryMass n + gnomonRepeatedCarryMass n +
      gnomonCofactorSemiprimeBudget n S + gnomonPascalShellHigherPrimePowerMass n =
    gnomonPascalOldLogBudget n +
      (gnomonCofactorSemiprimeBudget n S - gnomonCofactorWindowMass n) := by
  have h := gnomonPascalOldLogBudget_cofactor_excess hn
  linarith

theorem exists_prime_squareCell_of_semiprimeBudget_lt {n : ℕ} {S : Finset ℕ}
    (hn : 3 ≤ n) (hS : IsFinitePrimeBasis S) (hbound : ∀ q ∈ S, q ≤ 2 * n)
    (hstrict : gnomonPascalSmallCarryMass n + gnomonRepeatedCarryMass n +
      gnomonCofactorSemiprimeBudget n S + gnomonPascalShellHigherPrimePowerMass n <
        Real.log (GnomonPascalCell n : ℝ)) : ∃ p, p.Prime ∧ SquareCell n p := by
  apply (gnomonPascalOldLogBudget_lt_iff hn).mp
  have hb := gnomonCofactorWindowMass_le_semiprimeBudget hn hS hbound
  rw [gnomonPascalOldLogBudget_semiprime_excess hn S] at hstrict
  linarith

end DkMath.NumberTheory.Legendre
