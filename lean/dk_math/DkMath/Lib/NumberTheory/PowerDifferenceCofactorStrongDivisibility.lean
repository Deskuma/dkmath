/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.PowerDifferenceCofactorArithmetic
import DkMath.Lib.NumberTheory.PowerDifferenceCofactorGcd
import Mathlib.Data.Nat.DvdSequence

#print "file: DkMath.Lib.NumberTheory.PowerDifferenceCofactorStrongDivisibility"

/-!
# Strong divisibility of primitive-coordinate cofactors

[DkMath.Lib] GN-LIB-005b. The addition formula reduces a gcd by one index.
Primitiveness makes the extra coordinate power coprime to the other cofactor,
so Euclid's algorithm on indices is also Euclid's algorithm on values.
The proof organization follows Mathlib's Fibonacci strong-divisibility proof;
the arithmetic input here is the geometric cofactor addition formula.
-/

namespace DkMath.Lib.NumberTheory

open DkMath.Lib.Cosmic

/-- [DkMath.Lib] A positive-degree cofactor is coprime to its second coordinate.
The recurrence leaves x^(n-1) after removing a multiple of y. Degree zero
is excluded because R_0=0 need not be coprime to y. -/
theorem coprime_powerDifferenceCofactor_right
    {n x y : ℕ} (hn : 0 < n) (hxy : x.Coprime y) :
    (powerDifferenceCofactor n x y).Coprime y := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [powerDifferenceCofactor_succ, Nat.coprime_mul_left_add_left]
  exact hxy.pow_left k

/-- [DkMath.Lib] Coordinate symmetry gives the corresponding first-coordinate result. -/
theorem coprime_powerDifferenceCofactor_left
    {n x y : ℕ} (hn : 0 < n) (hxy : x.Coprime y) :
    (powerDifferenceCofactor n x y).Coprime x := by
  rw [powerDifferenceCofactor_symm]
  exact coprime_powerDifferenceCofactor_right hn hxy.symm

/-- [DkMath.Lib] Positive-degree primitive cofactors are coprime to xy. -/
theorem coprime_powerDifferenceCofactor_coordinates
    {n x y : ℕ} (hn : 0 < n) (hxy : x.Coprime y) :
    (powerDifferenceCofactor n x y).Coprime (x * y) :=
  (coprime_powerDifferenceCofactor_left hn hxy).mul_right
    (coprime_powerDifferenceCofactor_right hn hxy)

/-- [DkMath.Lib] One Euclidean index subtraction preserves the value gcd.
The y^m factor in the addition formula is removable only after using primitive
coordinates. The m=0 branch is treated separately, so all indices are included. -/
theorem gcd_powerDifferenceCofactor_add_self (m n x y : ℕ) (hxy : x.Coprime y) :
    Nat.gcd (powerDifferenceCofactor m x y) (powerDifferenceCofactor (n + m) x y) =
      Nat.gcd (powerDifferenceCofactor m x y) (powerDifferenceCofactor n x y) := by
  by_cases hm : m = 0
  · simp [hm]
  have hc : (y ^ m).Coprime (powerDifferenceCofactor m x y) :=
    (coprime_powerDifferenceCofactor_right (Nat.pos_of_ne_zero hm) hxy).symm.pow_left m
  rw [powerDifferenceCofactor_add,
    add_comm (x ^ n * powerDifferenceCofactor m x y), Nat.gcd_add_mul_right_right]
  exact hc.gcd_mul_left_cancel_right _

/-- [DkMath.Lib] Repeated index subtraction is the quotient step of Euclid's algorithm. -/
theorem gcd_powerDifferenceCofactor_add_mul_self (m n k x y : ℕ) (hxy : x.Coprime y) :
    Nat.gcd (powerDifferenceCofactor m x y) (powerDifferenceCofactor (n + k * m) x y) =
      Nat.gcd (powerDifferenceCofactor m x y) (powerDifferenceCofactor n x y) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, ← add_assoc, gcd_powerDifferenceCofactor_add_self _ _ _ _ hxy]
    exact ih

/-- [DkMath.Lib] The cofactor sequence is strongly divisible at primitive coordinates.
This is equality of the natural gcd, including zero indices; no positivity,
coordinate ordering or prime-index assumption is used. Without primitiveness
the coordinate powers removed in the Euclidean step can carry extra factors. -/
theorem gcd_powerDifferenceCofactor (m n x y : ℕ) (hxy : x.Coprime y) :
    Nat.gcd (powerDifferenceCofactor m x y) (powerDifferenceCofactor n x y) =
      powerDifferenceCofactor (Nat.gcd m n) x y := by
  induction m, n using Nat.gcd.induction with
  | H0 n => simp
  | H1 m n _ ih =>
    rw [← Nat.gcd_rec m n] at ih
    conv_lhs => rw [← Nat.mod_add_div' n m]
    rw [gcd_powerDifferenceCofactor_add_mul_self _ _ _ _ _ hxy, Nat.gcd_comm]
    exact ih

/-- [DkMath.Lib] Register the exact gcd theorem in Mathlib's strong-divisibility API. -/
theorem isStrongDvdSequence_powerDifferenceCofactor (x y : ℕ) (hxy : x.Coprime y) :
    Nat.IsStrongDvdSequence (fun n => powerDifferenceCofactor n x y) :=
  fun m n => gcd_powerDifferenceCofactor m n x y hxy

/-- [DkMath.Lib] Divisibility of indices gives divisibility of cofactors even for
nonprimitive coordinates. This weaker fact uses the product-of-degrees identity
alone; the stronger exact-gcd result above retains the primitive hypothesis. -/
theorem powerDifferenceCofactor_dvd_of_dvd {a b : ℕ} (hab : a ∣ b) (x y : ℕ) :
    powerDifferenceCofactor a x y ∣ powerDifferenceCofactor b x y := by
  obtain ⟨k, rfl⟩ := hab
  rw [Nat.mul_comm a k, powerDifferenceCofactor_mul]
  exact dvd_mul_left _ _

/-- [DkMath.Lib] Exact common factor of a cofactor and its borrowed correction.
The correction is xy R_n, not the completion deficit D_(n+2). The coordinate
factor xy cancels by coprimality; strong divisibility reduces the remaining
gcd to the index gcd with 2. The formula includes n=0. -/
theorem gcd_powerDifferenceCofactor_loan (n x y : ℕ) (hxy : x.Coprime y) :
    Nat.gcd (powerDifferenceCofactor (n + 2) x y)
        (x * y * powerDifferenceCofactor n x y) =
      powerDifferenceCofactor (Nat.gcd n 2) x y := by
  rw [(coprime_powerDifferenceCofactor_coordinates (by omega : 0 < n + 2) hxy).symm.gcd_mul_left_cancel_right,
    gcd_powerDifferenceCofactor _ _ _ _ hxy]
  rw [Nat.gcd_comm (n + 2) n, Nat.add_comm n 2, Nat.gcd_add_self_right]

/-- [DkMath.Lib] Odd-degree borrowing needs no common-factor normalization. -/
theorem gcd_powerDifferenceCofactor_loan_odd (k x y : ℕ) (hxy : x.Coprime y) :
    Nat.gcd (powerDifferenceCofactor (2 * k + 3) x y)
        (x * y * powerDifferenceCofactor (2 * k + 1) x y) = 1 := by
  rw [show 2 * k + 3 = (2 * k + 1) + 2 from by omega,
    gcd_powerDifferenceCofactor_loan _ _ _ hxy,
    show 2 * k + 1 = 1 + k * 2 from by omega, Nat.gcd_add_mul_right_left]
  simp

/-- [DkMath.Lib] Even-degree borrowing has exactly the common factor x+y.
This is the gcd with the borrowed correction, not the even-degree deficit gcd. -/
theorem gcd_powerDifferenceCofactor_loan_even (k x y : ℕ) (hxy : x.Coprime y) :
    Nat.gcd (powerDifferenceCofactor (2 * k + 4) x y)
        (x * y * powerDifferenceCofactor (2 * k + 2) x y) = x + y := by
  rw [show 2 * k + 4 = (2 * k + 2) + 2 from by omega,
    gcd_powerDifferenceCofactor_loan _ _ _ hxy]
  have hi : Nat.gcd (2 * k + 2) 2 = 2 :=
    Nat.gcd_eq_right_iff_dvd.mpr ⟨k + 1, by omega⟩
  rw [hi, powerDifferenceCofactor_two]

example : Nat.gcd (powerDifferenceCofactor 6 (5 : ℕ) 3)
    (powerDifferenceCofactor 9 (5 : ℕ) 3) = 49 := by decide
example : Nat.gcd (powerDifferenceCofactor 3 (6 : ℕ) 4)
    (powerDifferenceCofactor 4 (6 : ℕ) 4) = 4 := by decide
example : Nat.gcd (powerDifferenceCofactor 4 (5 : ℕ) 3)
    (15 * powerDifferenceCofactor 2 (5 : ℕ) 3) = 8 := by decide
example : Nat.gcd (powerDifferenceCofactor 4 (5 : ℕ) 3)
    (completionDefect 4 5 3) = 16 := by decide

end DkMath.Lib.NumberTheory
