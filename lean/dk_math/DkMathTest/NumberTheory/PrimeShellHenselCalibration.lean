/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimeShellHensel
import DkMath.NumberTheory.GNThreeHenselDepth
import DkMath.NumberTheory.GNThreePairedDepth
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

#print "file: DkMathTest.NumberTheory.PrimeShellHenselCalibration"

namespace DkMathTest.PrimeShellHensel

open Polynomial DkMath.NumberTheory DkMath.CosmicFormula

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The smallest prime degree has a simple linear shell, even at q=3. -/
example : ∃! t : Fin 3, (3 : ℤ) ^ 2 ∣ GTail 2 1 (1 + 3 * t.val : ℤ) 1 := by
  apply existsUnique_primeShell_powLift_digit (by decide) (by decide) (by decide)
    (by decide : 1 ≤ 1) 1 1
  · norm_num
  · norm_num [GTail, Finset.sum_range_succ, Nat.choose]

/-- A higher prime degree and a depth-two seed. -/
example : ∃! t : Fin 11, (11 : ℤ) ^ 3 ∣ GTail 5 1 (2 + 11 ^ 2 * t.val : ℤ) 1 := by
  apply existsUnique_primeShell_powLift_digit (by decide) (by decide) (by decide)
    (by decide : 1 ≤ 2) 1 2
  · norm_num
  · norm_num [GTail, Finset.sum_range_succ, Nat.choose]

theorem prime_five_all_depths (k : ℕ) :
    ∃ g : ℤ, (11 : ℤ) ^ (k + 1) ∣ GTail 5 1 g 1 := by
  apply exists_primeShell_pow_root (by decide) (by decide) (by decide) 1 2
  · norm_num
  · norm_num [GTail, Finset.sum_range_succ, Nat.choose]

theorem prime_five_exact_depth {k : ℕ} (hk : 1 ≤ k) :
    ∃ g : ℤ, (11 : ℤ) ^ k ∣ GTail 5 1 g 1 ∧
      ¬ (11 : ℤ) ^ (k + 1) ∣ GTail 5 1 g 1 := by
  apply exists_primeShell_exact_depth (by decide) (by decide) (by decide) hk 1 2
  · norm_num
  · norm_num [GTail, Finset.sum_range_succ, Nat.choose]

/-- Degree three recovers the existing derivative 2*g+3*u. -/
theorem cubic_derivative (g u : ℤ) :
    (primeShellPolynomial 3 u).derivative.eval g = 2 * g + 3 * u := by
  norm_num [primeShellPolynomial, GTail, Finset.sum_range_succ, derivative_pow]
  ring

/-- The old Nat cubic next-digit endpoint remains available. -/
example : ∃! t : Fin 7, 7 ^ 2 ∣ DkMath.CosmicFormulaBinom.GN 3 (1 + 7 * t.val) 1 := by
  apply existsUnique_GN_three_powLift_digit (by decide) (by decide : 1 ≤ 1)
  · norm_num [DkMath.CosmicFormulaBinom.GN, DkMath.CosmicFormula.GN,
      GTail, Finset.sum_range_succ, Nat.choose]
  · norm_num

/-- The generic integer API gives the corresponding cubic lift. -/
example : ∃! t : Fin 7, (7 : ℤ) ^ 2 ∣ GTail 3 1 (1 + 7 * t.val : ℤ) 1 := by
  apply existsUnique_primeShell_powLift_digit (by decide) (by decide) (by decide)
    (by decide : 1 ≤ 1) 1 1
  · norm_num
  · norm_num [GTail, Finset.sum_range_succ, Nat.choose]

example : GTail 3 1 (1 : ZMod 7) 1 = 0 ↔
    ((1 + 1 : ZMod 7) / 1) ^ 3 = 1 ∧ (1 + 1 : ZMod 7) / 1 ≠ 1 := by
  apply primeShell_root_iff
  · decide
  · decide

/-- Ramified degree-three roots are not simple. -/
example : GTail 3 1 (0 : ZMod 3) 1 = 0 :=
  (primeShell_ramified_root_iff (by decide) 0 1).mpr rfl

example : (3 : ℤ) ∣ (primeShellPolynomial 3 1).derivative.eval 0 := by
  rw [cubic_derivative]
  norm_num

/-- No ramified cubic digit lifts this root to depth two. -/
example : ¬ ∃ t : Fin 3, (3 : ℤ) ^ 2 ∣ GTail 3 1 (3 * t.val : ℤ) 1 := by
  rintro ⟨t, ht⟩
  fin_cases t <;> norm_num [GTail, Finset.sum_range_succ, Nat.choose] at ht

/-- A base divisible by q can have singular roots away from p. -/
example : GTail 3 1 (0 : ℤ) 0 = 0 ∧
    (7 : ℤ) ∣ (primeShellPolynomial 3 0).derivative.eval 0 := by
  rw [cubic_derivative]
  norm_num [GTail, Finset.sum_range_succ, Nat.choose]

end DkMathTest.PrimeShellHensel
