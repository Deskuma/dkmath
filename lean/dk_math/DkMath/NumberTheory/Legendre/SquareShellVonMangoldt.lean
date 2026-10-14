/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.GnomonPascalCell
import Mathlib.NumberTheory.Chebyshev

#print "file: DkMath.NumberTheory.Legendre.SquareShellVonMangoldt"

/-! Exact finite von Mangoldt and prime-birth decompositions of square shells. -/

namespace DkMath.NumberTheory.Legendre

open scoped BigOperators

/-- The classical von Mangoldt mass on the strict square shell. -/
noncomputable def gnomonPascalShellVonMangoldtMass (n : ℕ) : ℝ :=
  ∑ r ∈ squareOffsets n, ArithmeticFunction.vonMangoldt (n ^ 2 + r)

/-- Only nonprime prime powers contribute to the higher correction. -/
noncomputable def higherPrimePowerWeight (q : ℕ) : ℝ :=
  if IsPrimePow q ∧ ¬ q.Prime then ArithmeticFunction.vonMangoldt q else 0

/-- The exact shell correction, not the old Pascal carry budget. -/
noncomputable def gnomonPascalShellHigherPrimePowerMass (n : ℕ) : ℝ :=
  ∑ r ∈ squareOffsets n, higherPrimePowerWeight (n ^ 2 + r)

theorem higherPrimePowerWeight_nonneg (q : ℕ) : 0 ≤ higherPrimePowerWeight q := by
  unfold higherPrimePowerWeight
  split <;> simp [ArithmeticFunction.vonMangoldt_nonneg]

/-- The three cases are prime birth, nonprime prime power, and zero weight. -/
theorem vonMangoldt_eq_primeBirth_add_higher (q : ℕ) :
    ArithmeticFunction.vonMangoldt q =
      pascalPrimeBirthLogMass q + higherPrimePowerWeight q := by
  rw [pascalPrimeBirthLogMass_eq]
  by_cases hp : q.Prime
  · simp [hp, higherPrimePowerWeight, ArithmeticFunction.vonMangoldt_apply_prime hp]
  · by_cases hpp : IsPrimePow q
    · simp [hp, hpp, higherPrimePowerWeight]
    · simp [hp, hpp, higherPrimePowerWeight,
        ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]

theorem gnomonPascalShellVonMangoldtMass_nonneg (n : ℕ) :
    0 ≤ gnomonPascalShellVonMangoldtMass n := by
  exact Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg

theorem gnomonPascalShellHigherPrimePowerMass_nonneg (n : ℕ) :
    0 ≤ gnomonPascalShellHigherPrimePowerMass n := by
  exact Finset.sum_nonneg fun _ _ => higherPrimePowerWeight_nonneg _

/-- Exact birth/correction split at every anchor, including zero. -/
theorem gnomonPascalShellVonMangoldtMass_eq_birth_add_higher (n : ℕ) :
    gnomonPascalShellVonMangoldtMass n =
      gnomonPascalShellBirthLogMass n + gnomonPascalShellHigherPrimePowerMass n := by
  unfold gnomonPascalShellVonMangoldtMass gnomonPascalShellBirthLogMass
    gnomonPascalShellHigherPrimePowerMass
  simp only [vonMangoldt_eq_primeBirth_add_higher, Finset.sum_add_distrib]

/-- Shifted finite sums give the exact cumulative difference. -/
theorem squareOffsets_sum_eq_range_sub (n : ℕ) (f : ℕ → ℝ) :
    (∑ r ∈ squareOffsets n, f (n ^ 2 + r)) =
      (∑ q ∈ Finset.range (n ^ 2 + 2 * n + 1), f q) -
      ∑ q ∈ Finset.range (n ^ 2 + 1), f q := by
  have hs : (∑ r ∈ squareOffsets n, f (n ^ 2 + r)) =
      ∑ i ∈ Finset.range (2 * n), f (n ^ 2 + (i + 1)) := by
    unfold squareOffsets
    rw [← Finset.Ico_add_one_right_eq_Icc]
    simpa only [Nat.zero_add, Nat.Ico_zero_eq_range] using
      (Finset.sum_Ico_add' (fun r => f (n ^ 2 + r)) 0 (2 * n) 1).symm
  rw [hs]
  have ht := Finset.sum_range_add f (n ^ 2 + 1) (2 * n)
  have hi : n ^ 2 + 1 + 2 * n = n ^ 2 + 2 * n + 1 := by omega
  rw [hi] at ht
  have he : (fun i => f (n ^ 2 + 1 + i)) = (fun i => f (n ^ 2 + (i + 1))) := by
    funext i; congr 1; omega
  rw [he] at ht
  linarith

/-- Integer psi uses an exact initial segment, with no asymptotic input. -/
theorem psi_nat_eq_sum_range (N : ℕ) :
    Chebyshev.psi (N : ℝ) =
      ∑ q ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt q := by
  rw [Chebyshev.psi_eq_sum_Icc]
  simp only [Nat.floor_natCast]
  rw [← Finset.Ico_add_one_right_eq_Icc, Nat.Ico_zero_eq_range]

/-- Integer theta is the cumulative prime-birth mass. -/
theorem theta_nat_eq_sum_primeBirth_range (N : ℕ) :
    Chebyshev.theta (N : ℝ) =
      ∑ q ∈ Finset.range (N + 1), pascalPrimeBirthLogMass q := by
  rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  simp only [Nat.floor_natCast, pascalPrimeBirthLogMass_eq]
  rw [← Finset.Ico_add_one_right_eq_Icc, Nat.Ico_zero_eq_range]

/-- The strict shell ends at n squared plus twice n, not at the next square. -/
theorem gnomonPascalShellVonMangoldtMass_eq_psi_sub (n : ℕ) :
    gnomonPascalShellVonMangoldtMass n =
      Chebyshev.psi ((n ^ 2 + 2 * n : ℕ) : ℝ) - Chebyshev.psi ((n ^ 2 : ℕ) : ℝ) := by
  rw [psi_nat_eq_sum_range, psi_nat_eq_sum_range]
  exact squareOffsets_sum_eq_range_sub n _

/-- Prime birth is the corresponding exact theta increment. -/
theorem gnomonPascalShellBirthLogMass_eq_theta_sub (n : ℕ) :
    gnomonPascalShellBirthLogMass n =
      Chebyshev.theta ((n ^ 2 + 2 * n : ℕ) : ℝ) - Chebyshev.theta ((n ^ 2 : ℕ) : ℝ) := by
  rw [theta_nat_eq_sum_primeBirth_range, theta_nat_eq_sum_primeBirth_range]
  exact squareOffsets_sum_eq_range_sub n _

/-- The higher correction is precisely the shell increment of psi minus theta. -/
theorem gnomonPascalShellHigherPrimePowerMass_eq_psi_theta_sub (n : ℕ) :
    gnomonPascalShellHigherPrimePowerMass n =
      (Chebyshev.psi ((n ^ 2 + 2 * n : ℕ) : ℝ) - Chebyshev.theta ((n ^ 2 + 2 * n : ℕ) : ℝ)) -
      (Chebyshev.psi ((n ^ 2 : ℕ) : ℝ) - Chebyshev.theta ((n ^ 2 : ℕ) : ℝ)) := by
  have hs := gnomonPascalShellVonMangoldtMass_eq_birth_add_higher n
  rw [gnomonPascalShellVonMangoldtMass_eq_psi_sub,
    gnomonPascalShellBirthLogMass_eq_theta_sub] at hs
  linarith

@[simp] theorem gnomonPascalShellVonMangoldtMass_zero :
    gnomonPascalShellVonMangoldtMass 0 = 0 := by
  simp [gnomonPascalShellVonMangoldtMass, squareOffsets]

@[simp] theorem gnomonPascalShellHigherPrimePowerMass_zero :
    gnomonPascalShellHigherPrimePowerMass 0 = 0 := by
  simp [gnomonPascalShellHigherPrimePowerMass, squareOffsets]

end DkMath.NumberTheory.Legendre
