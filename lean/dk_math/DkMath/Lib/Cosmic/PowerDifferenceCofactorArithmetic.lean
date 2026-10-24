/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.PowerDifferenceCofactor

#print "file: DkMath.Lib.Cosmic.PowerDifferenceCofactorArithmetic"

/-!
# Cofactor arithmetic without division

[DkMath.Lib] GN-LIB-005b. Addition and multiplication of indices are finite-sum
identities in a commutative semiring. In particular, replacing x,y by x²,y²
reduces the index but increases the bases. This is not a strict height descent.
-/

namespace DkMath.Lib.Cosmic

/-- [DkMath.Lib] Swapping the two coordinates reverses the finite geometric sum.
No order relation, nonzero gap or cancellation hypothesis is used. -/
theorem powerDifferenceCofactor_symm
    {R : Type*} [CommSemiring R] (n : ℕ) (x y : R) :
    powerDifferenceCofactor n x y = powerDifferenceCofactor n y x := by
  unfold powerDifferenceCofactor
  rw [← Finset.sum_range_reflect (fun i => y ^ i * x ^ (n - 1 - i)) n]
  apply Finset.sum_congr rfl
  intro i hi
  have heq : n - 1 - (n - 1 - i) = i := by
    have := Finset.mem_range.mp hi
    omega
  rw [heq, mul_comm]

/-- [DkMath.Lib] Splitting the index into two blocks gives the addition formula.
The formula includes zero indices and diagonal or zero coordinates. -/
theorem powerDifferenceCofactor_add
    {R : Type*} [CommSemiring R] (a b : ℕ) (x y : R) :
    powerDifferenceCofactor (a + b) x y =
      x ^ a * powerDifferenceCofactor b x y + y ^ b * powerDifferenceCofactor a x y := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [show a + (b + 1) = (a + b) + 1 from by omega,
      powerDifferenceCofactor_succ, ih, powerDifferenceCofactor_succ, pow_add, pow_succ]
    ring

/-- [DkMath.Lib] Multiplication of indices factors into two geometric cofactors.
This finite identity replaces quotient cancellation and remains true when
x=y. It records the change of bases explicitly in R_a(x^b,y^b). -/
theorem powerDifferenceCofactor_mul
    {R : Type*} [CommSemiring R] (a b : ℕ) (x y : R) :
    powerDifferenceCofactor (a * b) x y =
      powerDifferenceCofactor a (x ^ b) (y ^ b) * powerDifferenceCofactor b x y := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, powerDifferenceCofactor_add, ih, powerDifferenceCofactor_succ]
    rw [show x ^ (a * b) = (x ^ b) ^ a by rw [← pow_mul, Nat.mul_comm]]
    ring

/-- [DkMath.Lib] Even-index factorization exposes exactly one sum factor.
The remaining cofactor uses squared bases; this is an identity, not a gcd or
maximal-valuation assertion. It includes index zero. -/
theorem powerDifferenceCofactor_even
    {R : Type*} [CommSemiring R] (m : ℕ) (x y : R) :
    powerDifferenceCofactor (2 * m) x y =
      (x + y) * powerDifferenceCofactor m (x ^ 2) (y ^ 2) := by
  rw [Nat.mul_comm 2 m, powerDifferenceCofactor_mul, powerDifferenceCofactor_two, mul_comm]

/-- [DkMath.Lib] Odd-index borrowing produces a square of the sum coordinate.
The correction is xy R_(2k+1), distinct from the completion deficit D_n.
This exposes a square factor in the borrowed sum and makes no claim that
R_(2k+3) itself is a square or that an FLT height decreases. -/
theorem powerDifferenceCofactor_square_loan
    {R : Type*} [CommSemiring R] (k : ℕ) (x y : R) :
    powerDifferenceCofactor (2 * k + 3) x y +
        x * y * powerDifferenceCofactor (2 * k + 1) x y =
      (x + y) ^ 2 * powerDifferenceCofactor (k + 1) (x ^ 2) (y ^ 2) := by
  have h := powerDifferenceCofactor_recurrence (2 * k + 1) x y
  rw [show 2 * k + 1 + 1 = 2 * (k + 1) from by omega,
    powerDifferenceCofactor_even] at h
  calc
    _ = (x + y) * ((x + y) * powerDifferenceCofactor (k + 1) (x ^ 2) (y ^ 2)) := h
    _ = _ := by ring

example : powerDifferenceCofactor 6 (5 : ℕ) 3 = 8 * powerDifferenceCofactor 3 25 9 := by decide
example : powerDifferenceCofactor 5 (5 : ℕ) 3 + 15 * powerDifferenceCofactor 3 5 3 =
    64 * powerDifferenceCofactor 2 25 9 := by decide
example : powerDifferenceCofactor 4 (2 : ℕ) 2 = 32 := by decide

end DkMath.Lib.Cosmic
