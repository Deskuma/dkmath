/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GNSuccessor

#print "file: DkMath.Lib.Cosmic.PowerDifferenceCofactor"

/-!
# Power-difference cofactor: the division-free R sequence

[DkMath.Lib] GN-LIB-004 builds the finite geometric cofactor from the shell
identity B22. The definition uses no division, hence includes equal coordinates,
zero coordinates and degree zero over an arbitrary commutative semiring.
The GN bridge is a coordinate translation, not cancellation of `x - y`.
-/

namespace DkMath.Lib.Cosmic

open DkMath.CosmicFormula

/-- [DkMath.Lib] The homogeneous geometric sum R_n(x,y).
Its degree is n-1 for positive n; the empty sum R_0 is zero. This definition
continues to make sense on the diagonal, unlike a quotient by x-y. -/
def powerDifferenceCofactor {R : Type*} [CommSemiring R] (n : ℕ) (x y : R) : R :=
  ∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)

/-- [DkMath.Lib] The empty cofactor is zero. -/
@[simp] theorem powerDifferenceCofactor_zero {R : Type*} [CommSemiring R] (x y : R) :
    powerDifferenceCofactor 0 x y = 0 := by simp [powerDifferenceCofactor]

/-- [DkMath.Lib] The degree-one cofactor is one, including zero coordinates. -/
@[simp] theorem powerDifferenceCofactor_one {R : Type*} [CommSemiring R] (x y : R) :
    powerDifferenceCofactor 1 x y = 1 := by simp [powerDifferenceCofactor]

/-- [DkMath.Lib] B22 translated to sum coordinates, without subtraction.
This is the semiring bridge; it is valid even when g=0. -/
theorem powerDifferenceCofactor_add_eq_GTail
    {R : Type*} [CommSemiring R] (n : ℕ) (g y : R) :
    powerDifferenceCofactor n (g + y) y = GTail n 1 g y := by
  rw [GTail_one_eq_GTailCyclotomicShell]
  rfl

/-- [DkMath.Lib] Ring coordinates recover R_n(x,y) from GN at gap x-y.
No nonzero hypothesis on the gap is needed. -/
theorem powerDifferenceCofactor_eq_GTail_sub
    {R : Type*} [CommRing R] (n : ℕ) (x y : R) :
    powerDifferenceCofactor n x y = GTail n 1 (x - y) y := by
  simpa only [sub_add_cancel] using powerDifferenceCofactor_add_eq_GTail n (x - y) y

/-- [DkMath.Lib] Natural subtraction is a coordinate translation only when y≤x.
The finite-sum definition itself needs no ordering of the two coordinates. -/
theorem powerDifferenceCofactor_eq_GTail_nat_sub
    (n x y : ℕ) (hyx : y ≤ x) :
    powerDifferenceCofactor n x y = GTail n 1 (x - y) y := by
  simpa only [Nat.sub_add_cancel hyx] using
    powerDifferenceCofactor_add_eq_GTail n (x - y) y

/-- [DkMath.Lib] The existing GN successor law transported to R coordinates.
This reuses `GN_succ_right` directly. Arbitrary semiring coordinates need not
admit a difference g with x=g+y; the following finite-sum successor theorem
also covers those coordinates without adding a subtraction hypothesis. -/
theorem powerDifferenceCofactor_add_succ
    {R : Type*} [CommSemiring R] (n : ℕ) (g y : R) :
    powerDifferenceCofactor (n + 1) (g + y) y =
      y * powerDifferenceCofactor n (g + y) y + (g + y) ^ n := by
  simp only [powerDifferenceCofactor_add_eq_GTail]
  exact DkMath.NumberTheory.GapFocusing.GN_succ_right n g y

/-- [DkMath.Lib] Peeling the final summand gives R_(n+1)=y R_n+x^n.
This is the finite-sum recurrence underlying the existing GN successor law. -/
theorem powerDifferenceCofactor_succ
    {R : Type*} [CommSemiring R] (n : ℕ) (x y : R) :
    powerDifferenceCofactor (n + 1) x y = y * powerDifferenceCofactor n x y + x ^ n := by
  unfold powerDifferenceCofactor
  rw [Finset.sum_range_succ, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have h : n + 1 - 1 - i = n - 1 - i + 1 := by
      have := Finset.mem_range.mp hi
      omega
    rw [h, pow_succ]
    ring
  · simp

/-- [DkMath.Lib] The quadratic cofactor is x+y. -/
@[simp] theorem powerDifferenceCofactor_two {R : Type*} [CommSemiring R] (x y : R) :
    powerDifferenceCofactor 2 x y = x + y := by
  rw [show 2 = 1 + 1 from rfl, powerDifferenceCofactor_succ]
  simp [add_comm]

/-- [DkMath.Lib] The second-order recurrence in cancellation-free form.
Two successive geometric recurrences eliminate x^n. All operations remain
semiring operations; positivity and integral-domain hypotheses are unnecessary. -/
theorem powerDifferenceCofactor_recurrence
    {R : Type*} [CommSemiring R] (k : ℕ) (x y : R) :
    powerDifferenceCofactor (k + 2) x y + x * y * powerDifferenceCofactor k x y =
      (x + y) * powerDifferenceCofactor (k + 1) x y := by
  rw [show k + 2 = (k + 1) + 1 from rfl, powerDifferenceCofactor_succ, pow_succ]
  calc
    y * powerDifferenceCofactor (k + 1) x y + x ^ k * x +
        x * y * powerDifferenceCofactor k x y =
      y * powerDifferenceCofactor (k + 1) x y +
        x * (y * powerDifferenceCofactor k x y + x ^ k) := by ring
    _ = (x + y) * powerDifferenceCofactor (k + 1) x y := by
      rw [← powerDifferenceCofactor_succ]
      ring

/-- [DkMath.Lib] Multiplication by the gap reconstructs the two powers.
This ring identity is not a division formula and holds on the diagonal. -/
theorem sub_mul_powerDifferenceCofactor
    {R : Type*} [CommRing R] (n : ℕ) (x y : R) :
    (x - y) * powerDifferenceCofactor n x y = x ^ n - y ^ n := by
  rw [powerDifferenceCofactor_eq_GTail_sub]
  have h := add_pow_eq_mul_GTail_one_add_gap n (x - y) y
  rw [sub_add_cancel] at h
  linear_combination -h

/-- [DkMath.Lib] On the diagonal the n identical summands remain meaningful. -/
theorem powerDifferenceCofactor_diagonal
    {R : Type*} [CommSemiring R] (n : ℕ) (x : R) :
    powerDifferenceCofactor n x x = n * x ^ (n - 1) := by
  unfold powerDifferenceCofactor
  calc
    (∑ i ∈ Finset.range n, x ^ i * x ^ (n - 1 - i)) =
        ∑ _i ∈ Finset.range n, x ^ (n - 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← pow_add, Nat.add_sub_of_le]
      have := Finset.mem_range.mp hi
      omega
    _ = _ := by simp

/-- [DkMath.Lib] Natural cofactors lie below the full (x+y)^(n-1) budget.
For n=0 the assertion is 0≤1. For positive degrees the nonnegative correction
xy R_k in the second-order recurrence proves the induction step. -/
theorem powerDifferenceCofactor_le (n x y : ℕ) :
    powerDifferenceCofactor n x y ≤ (x + y) ^ (n - 1) := by
  cases n with
  | zero => simp
  | succ n =>
    induction n with
    | zero => simp
    | succ k ih =>
      have h := powerDifferenceCofactor_recurrence k x y
      have hb : (x + y) * powerDifferenceCofactor (k + 1) x y ≤
          (x + y) * (x + y) ^ k :=
        Nat.mul_le_mul_left (x + y) (by simpa using ih)
      change powerDifferenceCofactor (k + 2) x y ≤ (x + y) ^ (k + 1)
      rw [pow_succ']
      exact le_trans (Nat.le.intro h) hb

/-- [DkMath.Lib] A positive first coordinate ensures positive positive-degree R.
This sufficient condition will supply the correction term in deficit positivity. -/
theorem powerDifferenceCofactor_pos (k x y : ℕ) (hx : 0 < x) :
    0 < powerDifferenceCofactor (k + 1) x y := by
  rw [powerDifferenceCofactor_succ]
  exact Nat.add_pos_right _ (pow_pos hx k)

/-! Concrete values include a square at degree 3 and, with a different base,
a cube at degree 3. No claim excluding other perfect powers is intended. -/
example : powerDifferenceCofactor 3 (5 : ℕ) 3 = 49 := by decide
example : powerDifferenceCofactor 3 (18 : ℕ) 1 = 343 := by decide
example : powerDifferenceCofactor 3 (2 : ℕ) 2 = 12 := by decide
example : powerDifferenceCofactor 0 (0 : ℕ) 0 = 0 := by simp

end DkMath.Lib.Cosmic
