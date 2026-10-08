/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.Basic
import DkMath.NumberTheory.PascalPrebirthBirth
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.BigOperators.Intervals

#print "file: DkMath.NumberTheory.Legendre.GnomonPascalCell"

/-! Exact Pascal-cell and prime-birth interfaces for open square shells.
These equivalences restate prime existence; none proves a universal provider. -/

namespace DkMath.NumberTheory.Legendre

open scoped BigOperators

/-- The Pascal cell whose factorial numerator is the open square shell. -/
def GnomonPascalCell (n : ℕ) : ℕ := Nat.choose (n ^ 2 + 2 * n) (2 * n)

/-- Exact factorial interpretation as a product of the shell's consecutive points. -/
theorem gnomonPascalCell_mul_factorial (n : ℕ) :
    GnomonPascalCell n * (2 * n).factorial =
      ∏ i ∈ Finset.range (2 * n), (n ^ 2 + (i + 1)) := by
  calc
    _ = (n ^ 2 + 1).ascFactorial (2 * n) := by
      simpa [GnomonPascalCell, Nat.mul_comm] using
        (Nat.ascFactorial_eq_factorial_mul_choose (n ^ 2) (2 * n)).symm
    _ = _ := by simp only [Nat.ascFactorial_eq_prod_range, Nat.add_assoc, Nat.add_comm 1]

/-- Fresh primes divide this cell exactly when they lie in its square shell. -/
theorem prime_dvd_gnomonPascalCell_iff {n p : ℕ} (hn : 3 ≤ n)
    (hp : p.Prime) (hfresh : n ^ 2 < p) :
    p ∣ GnomonPascalCell n ↔ SquareCell n p := by
  have hsmall : 2 * n < p := by nlinarith
  have hkn : 2 * n ≤ n ^ 2 + 2 * n := by omega
  constructor
  · intro hdiv
    have hfac := (hp.dvd_iff_one_le_factorization (Nat.choose_ne_zero hkn)).mp hdiv
    have htop : p ≤ n ^ 2 + 2 * n := by
      by_contra h
      have hz := Nat.factorization_choose_eq_zero_of_lt (k := 2 * n) (by omega : n ^ 2 + 2 * n < p)
      omega
    exact ⟨hfresh, by nlinarith⟩
  · intro hcell
    apply hp.dvd_choose hsmall
    · simpa using hfresh
    · dsimp [SquareCell] at hcell
      nlinarith [hcell.2]

/-- The fresh-prime factor target is exactly shell prime existence. -/
theorem exists_prime_squareCell_iff_gnomonPascalCell {n : ℕ} (hn : 3 ≤ n) :
    (∃ p, p.Prime ∧ SquareCell n p) ↔
      ∃ p, p.Prime ∧ n ^ 2 < p ∧ p ∣ GnomonPascalCell n := by
  constructor
  · rintro ⟨p, hp, hcell⟩
    exact ⟨p, hp, hcell.1, (prime_dvd_gnomonPascalCell_iff hn hp hcell.1).mpr hcell⟩
  · rintro ⟨p, hp, hfresh, hdiv⟩
    exact ⟨p, hp, (prime_dvd_gnomonPascalCell_iff hn hp hfresh).mp hdiv⟩

/-- The geometric cell-index ratio shrinks with the anchor; zero is excluded. -/
theorem gnomonPascalCell_ratio {n : ℕ} (hn : 0 < n) :
    (2 * n : ℚ) / ((n : ℚ) ^ 2 + 2 * n) = 2 / ((n : ℚ) + 2) := by
  have hpos : (0 : ℚ) < n := by exact_mod_cast hn
  field_simp

/-- Exact carry count for every prime coordinate of the gnomon Pascal cell. -/
theorem gnomonPascalCell_factorization_carries {n p b : ℕ} (hp : p.Prime)
    (hb : Nat.log p (n ^ 2 + 2 * n) < b) :
    (GnomonPascalCell n).factorization p =
      ((Finset.Ico 1 b).filter (fun i => p ^ i ≤ (2 * n) % p ^ i + n ^ 2 % p ^ i)).card := by
  simpa [GnomonPascalCell] using
    (Nat.factorization_choose hp (by omega : 2 * n ≤ n ^ 2 + 2 * n) hb)

/-- In the fresh range the carry height is at most one. -/
theorem gnomonPascalCell_fresh_height_le_one {n p : ℕ} (hn : 3 ≤ n)
    (hfresh : n ^ 2 < p) : (GnomonPascalCell n).factorization p ≤ 1 := by
  apply Nat.factorization_choose_le_one
  have hsmall : 2 * n ≤ n ^ 2 := by nlinarith
  have hbase : 3 ≤ p := by nlinarith
  nlinarith

/-- A fresh prime in the shell occurs with exact carry height one. -/
theorem gnomonPascalCell_fresh_height_eq_one {n p : ℕ} (hn : 3 ≤ n)
    (hp : p.Prime) (hcell : SquareCell n p) :
    (GnomonPascalCell n).factorization p = 1 := by
  have hlo := (hp.dvd_iff_one_le_factorization
    (Nat.choose_ne_zero (by omega : 2 * n ≤ n ^ 2 + 2 * n))).mp
    ((prime_dvd_gnomonPascalCell_iff hn hp hcell.1).mpr hcell)
  exact Nat.le_antisymm (gnomonPascalCell_fresh_height_le_one hn hcell.1) hlo

/-- Prime-only Pascal birth log mass in the finite open square shell. -/
noncomputable def gnomonPascalShellBirthLogMass (n : ℕ) : ℝ :=
  ∑ r ∈ squareOffsets n, pascalPrimeBirthLogMass (n ^ 2 + r)

/-- Shell birth mass is nonnegative. -/
theorem gnomonPascalShellBirthLogMass_nonneg (n : ℕ) :
    0 ≤ gnomonPascalShellBirthLogMass n :=
  Finset.sum_nonneg (fun _ _ => pascalPrimeBirthLogMass_nonneg _)

/-- Positive shell birth mass is precisely a prime witness, not an existence proof. -/
theorem gnomonPascalShellBirthLogMass_pos_iff (n : ℕ) :
    0 < gnomonPascalShellBirthLogMass n ↔ ∃ p, p.Prime ∧ SquareCell n p := by
  rw [gnomonPascalShellBirthLogMass, Finset.sum_pos_iff_of_nonneg
    (fun r _ => pascalPrimeBirthLogMass_nonneg (n ^ 2 + r))]
  constructor
  · rintro ⟨r, hr, hpos⟩
    exact ⟨n ^ 2 + r, (pascalPrimeBirthLogMass_pos_iff _).mp hpos,
      (squareCell_iff_exists_squareOffset _ _).mpr ⟨r, mem_squareOffsets.mp hr, rfl⟩⟩
  · rintro ⟨p, hp, hcell⟩
    obtain ⟨r, hr, rfl⟩ := (squareCell_iff_exists_squareOffset _ _).mp hcell
    exact ⟨r, mem_squareOffsets.mpr hr, (pascalPrimeBirthLogMass_pos_iff _).mpr hp⟩

/-- Pointwise equality of fresh carry log weight and prime-only birth weight. -/
theorem gnomonPascalCell_fresh_logWeight {n r : ℕ} (hn : 3 ≤ n) (hr : r ∈ squareOffsets n) :
    ((GnomonPascalCell n).factorization (n ^ 2 + r) : ℝ) * Real.log (n ^ 2 + r : ℝ) =
      pascalPrimeBirthLogMass (n ^ 2 + r) := by
  rw [pascalPrimeBirthLogMass_eq]
  by_cases hp : (n ^ 2 + r).Prime
  · rw [ite_eq_left hp, gnomonPascalCell_fresh_height_eq_one hn hp
      ((squareCell_iff_exists_squareOffset _ _).mpr ⟨r, mem_squareOffsets.mp hr, rfl⟩)]
    simp
  · rw [ite_eq_right hp, Nat.factorization_eq_zero_of_not_prime _ hp]
    simp

/-- The fresh carry ledger has exactly the shell's prime birth log mass. -/
theorem gnomonPascalCell_fresh_logLedger {n : ℕ} (hn : 3 ≤ n) :
    (∑ r ∈ squareOffsets n, ((GnomonPascalCell n).factorization (n ^ 2 + r) : ℝ) *
      Real.log (n ^ 2 + r : ℝ)) = gnomonPascalShellBirthLogMass n := by
  exact Finset.sum_congr rfl (fun r hr => gnomonPascalCell_fresh_logWeight hn hr)

/-- The old-coordinate budget includes every prime at most the square, with full height.
This cutoff is larger than the old wave cutoff n used by capacity modules. -/
noncomputable def gnomonPascalOldLogBudget (n : ℕ) : ℝ :=
  ∑ p ∈ Finset.range (n ^ 2 + 1), ((GnomonPascalCell n).factorization p : ℝ) * Real.log (p : ℝ)

/-- Exact full prime-power log ledger in the bounded row support. -/
theorem gnomonPascalCell_log_factorization (n : ℕ) :
    Real.log (GnomonPascalCell n : ℝ) =
      ∑ p ∈ Finset.range (n ^ 2 + 2 * n + 1),
        ((GnomonPascalCell n).factorization p : ℝ) * Real.log (p : ℝ) := by
  classical
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  apply Finset.sum_subset
  · intro p hp
    rw [Finset.mem_range]
    by_contra h
    have hz : (GnomonPascalCell n).factorization p = 0 :=
      Nat.factorization_choose_eq_zero_of_lt (by omega)
    exact (Finsupp.mem_support_iff.mp hp) hz
  · intro p _ hp
    have hz := Finsupp.notMem_support_iff.mp hp
    simp [hz]

/-- The offset shell is exactly the range of positive successor offsets. -/
theorem gnomonPascalShellBirthLogMass_eq_range (n : ℕ) :
    gnomonPascalShellBirthLogMass n =
      ∑ i ∈ Finset.range (2 * n), pascalPrimeBirthLogMass (n ^ 2 + (i + 1)) := by
  unfold gnomonPascalShellBirthLogMass squareOffsets
  rw [← Finset.Ico_add_one_right_eq_Icc]
  simpa only [Nat.zero_add, Nat.Ico_zero_eq_range] using
    (Finset.sum_Ico_add' (fun r => pascalPrimeBirthLogMass (n ^ 2 + r)) 0 (2 * n) 1).symm

/-- Growth splits exactly into the old prime-power budget and fresh prime birth mass.
There are no remaining fresh cancellation terms; a strict old-budget bound is missing. -/
theorem gnomonPascalCell_log_eq_old_add_birth {n : ℕ} (hn : 3 ≤ n) :
    Real.log (GnomonPascalCell n : ℝ) =
      gnomonPascalOldLogBudget n + gnomonPascalShellBirthLogMass n := by
  rw [gnomonPascalCell_log_factorization,
    show n ^ 2 + 2 * n + 1 = (n ^ 2 + 1) + 2 * n by omega,
    Finset.sum_range_add, gnomonPascalShellBirthLogMass_eq_range]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hr : i + 1 ∈ squareOffsets n := mem_squareOffsets.mpr ⟨by omega, by
    have := Finset.mem_range.mp hi; omega⟩
  simpa only [Nat.add_assoc, Nat.add_comm 1, Nat.cast_add, Nat.cast_pow, Nat.cast_one, add_assoc, add_comm (1 : ℝ)] using gnomonPascalCell_fresh_logWeight hn hr

/-- A strict old-budget deficit is equivalent to a shell prime, not a proved bound. -/
theorem gnomonPascalOldLogBudget_lt_iff {n : ℕ} (hn : 3 ≤ n) :
    gnomonPascalOldLogBudget n < Real.log (GnomonPascalCell n : ℝ) ↔
      ∃ p, p.Prime ∧ SquareCell n p := by
  rw [gnomonPascalCell_log_eq_old_add_birth hn, lt_add_iff_pos_right,
    gnomonPascalShellBirthLogMass_pos_iff]

/-- A global reduction names the missing strict carry-budget bound explicitly.
The two small anchors are checked separately; this theorem proves no such bound. -/
theorem legendreConjecture_iff_pascalOldBudget :
    LegendreConjecture ↔ ∀ n : ℕ, 3 ≤ n →
      gnomonPascalOldLogBudget n < Real.log (GnomonPascalCell n : ℝ) := by
  constructor
  · intro H n hn
    exact (gnomonPascalOldLogBudget_lt_iff hn).mpr (H n (by omega))
  · intro H n hn
    by_cases h3 : 3 ≤ n
    · exact (gnomonPascalOldLogBudget_lt_iff h3).mp (H n h3)
    · have hsmall : n = 1 ∨ n = 2 := by omega
      rcases hsmall with rfl | rfl
      · exact ⟨2, by norm_num, by norm_num [SquareCell]⟩
      · exact ⟨5, by norm_num, by norm_num [SquareCell]⟩

end DkMath.NumberTheory.Legendre
