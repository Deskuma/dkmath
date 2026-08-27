/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Algebra.Group.ForwardDiff

#print "file: DkMath.CFBRC.Regularization.ForwardDifference"

/-!
# CFBRC finite forward-difference regularization

This module contains the zeta-independent finite kernel used by the first
CFBRC analytic-continuation audit.  It does not import the Riemann zeta
function, Dirichlet eta, or any RH module.

For the polynomial moment `x ↦ x^m`, every forward difference of order
strictly greater than `m` vanishes.  Hence the Euler-transformed alternating
value at a non-positive integer is represented by a genuinely finite sum.
-/

namespace DkMath.CFBRC.Regularization

open scoped BigOperators fwdDiff

/-- Euler's coefficient for the `j`-th forward difference. -/
def eulerForwardWeight (j : ℕ) : ℚ :=
  (-1 : ℚ) ^ j / (2 : ℚ) ^ (j + 1)

/--
The `j`-th unit forward difference of `x ↦ x^m`, evaluated at `x = 1`.
-/
def powerMomentForwardDifference (m j : ℕ) : ℚ :=
  (Δ_[(1 : ℚ)]^[j] (fun x : ℚ ↦ x ^ m)) 1

@[simp] theorem powerMomentForwardDifference_zero_order (m : ℕ) :
    powerMomentForwardDifference m 0 = 1 := by
  simp [powerMomentForwardDifference]

/-- A polynomial moment has no forward differences above its degree. -/
theorem powerMomentForwardDifference_eq_zero_of_lt
    {m j : ℕ} (h : m < j) :
    powerMomentForwardDifference m j = 0 := by
  have hzero := congrFun
    (fwdDiff_iter_pow_eq_zero_of_lt (R := ℚ) h) 1
  simpa [powerMomentForwardDifference] using hzero

/-- Only the first `m + 1` Euler coefficients can contribute to degree `m`. -/
theorem powerMomentForwardDifference_eq_zero_of_add_one_le
    {m j : ℕ} (h : m + 1 ≤ j) :
    powerMomentForwardDifference m j = 0 :=
  powerMomentForwardDifference_eq_zero_of_lt (Nat.lt_of_succ_le h)

end DkMath.CFBRC.Regularization
