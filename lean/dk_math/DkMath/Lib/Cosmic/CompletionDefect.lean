/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.PowerDifferenceCofactor

#print "file: DkMath.Lib.Cosmic.CompletionDefect"

/-!
# Completion deficit: a signed ring quantity and a bounded natural difference

[DkMath.Lib] GN-LIB-004. Write s=x+y and R_n for the geometric cofactor.
For n≥1 the budget is s^(n-1). The deficit D_n is the amount by which R_n
falls short of this budget. It differs from the Gap u^n added to a GN Body.

Natural subtraction is used only after the cofactor upper bound has been
proved. Ring subtraction is a separate signed definition; neither definition
asserts that an arbitrary cofactor cannot be another perfect power.
-/

namespace DkMath.Lib.Cosmic

/-- [DkMath.Lib] Signed completion deficit in a commutative ring.
At degree zero the exponent n-1 is truncated, giving D_0=1. The intended
homogeneous degree n-1 interpretation starts at n=1. -/
def signedCompletionDefect {R : Type*} [CommRing R] (n : ℕ) (x y : R) : R :=
  (x + y) ^ (n - 1) - powerDifferenceCofactor n x y

/-- [DkMath.Lib] Ring reconstruction retains both the cofactor and deficit. -/
theorem signedCompletionDefect_add_cofactor
    {R : Type*} [CommRing R] (n : ℕ) (x y : R) :
    signedCompletionDefect n x y + powerDifferenceCofactor n x y =
      (x + y) ^ (n - 1) := by
  exact sub_add_cancel _ _

/-- [DkMath.Lib] Signed deficit recurrence, translated from the R recurrence.
The k+3 indexing avoids the degree-zero truncated exponent convention. -/
theorem signedCompletionDefect_recurrence
    {R : Type*} [CommRing R] (k : ℕ) (x y : R) :
    signedCompletionDefect (k + 3) x y =
      (x + y) * signedCompletionDefect (k + 2) x y +
        x * y * powerDifferenceCofactor (k + 1) x y := by
  have h := powerDifferenceCofactor_recurrence (k + 1) x y
  unfold signedCompletionDefect
  rw [show k + 3 - 1 = (k + 1) + 1 from by omega,
    show k + 2 - 1 = k + 1 from by omega, pow_succ']
  linear_combination -h

/-- [DkMath.Lib] Nonnegative completion deficit over naturals.
The previously established `powerDifferenceCofactor_le` makes this difference
exact: adding R_n back recovers the whole budget, without information loss. -/
def completionDefect (n x y : ℕ) : ℕ :=
  (x + y) ^ (n - 1) - powerDifferenceCofactor n x y

/-- [DkMath.Lib] Exact natural reconstruction; the upper bound prevents clipping. -/
theorem completionDefect_add_cofactor (n x y : ℕ) :
    completionDefect n x y + powerDifferenceCofactor n x y =
      (x + y) ^ (n - 1) := by
  exact Nat.sub_add_cancel (powerDifferenceCofactor_le n x y)

/-- [DkMath.Lib] Natural degree-zero convention: R_0=0 and D_0=1. -/
@[simp] theorem completionDefect_zero (x y : ℕ) : completionDefect 0 x y = 1 := by
  simp [completionDefect]

/-- [DkMath.Lib] No deficit in degree one. -/
@[simp] theorem completionDefect_one (x y : ℕ) : completionDefect 1 x y = 0 := by
  simp [completionDefect]

/-- [DkMath.Lib] No deficit in degree two: R_2=x+y already fills the budget. -/
@[simp] theorem completionDefect_two (x y : ℕ) : completionDefect 2 x y = 0 := by
  simp [completionDefect]

/-- [DkMath.Lib] The natural deficit has a positive correction recurrence.
Using exact reconstruction twice transports the cancellation-free R recurrence.
No subtraction distribution or silent clipping of a negative quantity is used. -/
theorem completionDefect_recurrence (k x y : ℕ) :
    completionDefect (k + 3) x y =
      (x + y) * completionDefect (k + 2) x y +
        x * y * powerDifferenceCofactor (k + 1) x y := by
  have hnext := completionDefect_add_cofactor (k + 3) x y
  have hprev := completionDefect_add_cofactor (k + 2) x y
  have hrec := powerDifferenceCofactor_recurrence (k + 1) x y
  have hpow : (x + y) ^ (k + 2) = (x + y) * (x + y) ^ (k + 1) := pow_succ' _ _
  simp only [show k + 3 - 1 = k + 2 from by omega,
    show k + 2 - 1 = k + 1 from by omega] at hnext hprev
  nlinarith

/-- [DkMath.Lib] The first nonzero deficit is exactly xy. -/
@[simp] theorem completionDefect_three (x y : ℕ) : completionDefect 3 x y = x * y := by
  simpa using completionDefect_recurrence 0 x y

/-- [DkMath.Lib] Positive coordinates force a strictly positive deficit for n≥3.
Both positivity guards matter: a zero coordinate can fill the budget exactly.
The correction xy R_(k+1) is already positive, so no descent argument is needed. -/
theorem completionDefect_pos {n x y : ℕ} (hn : 3 ≤ n) (hx : 0 < x) (hy : 0 < y) :
    0 < completionDefect n x y := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 3 + k = k + 3 from Nat.add_comm _ _, completionDefect_recurrence]
  exact Nat.add_pos_right _ (Nat.mul_pos (Nat.mul_pos hx hy)
    (powerDifferenceCofactor_pos k x y hx))

/-- [DkMath.Lib] Positive deficit means strict shortfall from the budget.
This conclusion compares with (x+y)^(n-1), not with every possible perfect power. -/
theorem powerDifferenceCofactor_lt {n x y : ℕ}
    (hn : 3 ≤ n) (hx : 0 < x) (hy : 0 < y) :
    powerDifferenceCofactor n x y < (x + y) ^ (n - 1) := by
  have := completionDefect_pos hn hx hy
  have := completionDefect_add_cofactor n x y
  omega

/-- [DkMath.Lib] Casting the bounded natural deficit agrees with ring subtraction.
The cofactor bound is the essential guard in `Nat.cast_sub`; this bridge makes
explicit why the signed and natural definitions agree on natural coordinates. -/
theorem cast_completionDefect {R : Type*} [CommRing R] (n x y : ℕ) :
    (completionDefect n x y : R) = signedCompletionDefect n (x : R) (y : R) := by
  unfold completionDefect signedCompletionDefect
  rw [Nat.cast_sub (powerDifferenceCofactor_le n x y)]
  simp only [Nat.cast_pow, Nat.cast_add, powerDifferenceCofactor, Nat.cast_sum, Nat.cast_mul]

/-! ## Textbook examples and boundaries -/
example : completionDefect 3 5 3 = 15 := by decide
example : powerDifferenceCofactor 3 (5 : ℕ) 3 + completionDefect 3 5 3 = 64 := by decide
example : powerDifferenceCofactor 3 (18 : ℕ) 1 = 7 ^ 3 ∧
    completionDefect 3 18 1 = 18 := by decide
example : completionDefect 3 0 5 = 0 := by decide
example : completionDefect 4 2 2 = 32 := by decide
example : signedCompletionDefect 3 (-2 : ℤ) 3 = -6 := by decide
example : completionDefect 0 0 0 = 1 ∧ completionDefect 1 0 0 = 0 ∧
    completionDefect 2 0 0 = 0 := by decide

end DkMath.Lib.Cosmic
