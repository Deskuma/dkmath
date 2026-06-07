/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

#print "file: DkMath.DHNT.DynamicArithmeticSequence"

namespace DkMath
namespace DHNT

/-!
# Dynamic arithmetic sequences

This file records the algebraic core of the Python
`dynamic_arithmetic_sequence` demo.

The Lean-side normal form does not use `log` or `exp`.  The dynamic parameter
`k` simply rescales the common difference:

`a + i * (d * k)`.
-/

variable {C : Type*}

/-- The `k`-scaled common difference. -/
def dynamicStep [Mul C] (d k : C) : C :=
  d * k

/-- The `i`-th term of an ordinary arithmetic sequence. -/
def arithmeticTerm [Semiring C] (a d : C) (i : ℕ) : C :=
  a + (i : C) * d

/-- The `i`-th term of a dynamic arithmetic sequence. -/
def dynamicTerm [Semiring C] (a d k : C) (i : ℕ) : C :=
  arithmeticTerm a (dynamicStep d k) i

/-- The dynamic sequence as a finite list of its first `n` terms. -/
def dynamicSequence [Semiring C] (a d k : C) (n : ℕ) : List C :=
  (List.range n).map fun i => dynamicTerm a d k i

/-- Dynamic arithmetic is ordinary arithmetic with common difference `d * k`. -/
@[simp] theorem dynamicTerm_eq_arithmeticTerm_scaledDiff
    [Semiring C] (a d k : C) (i : ℕ) :
    dynamicTerm a d k i = arithmeticTerm a (d * k) i := by
  rfl

/-- The `k = 1` specialization recovers the ordinary arithmetic sequence. -/
@[simp] theorem dynamicTerm_one
    [Semiring C] (a d : C) (i : ℕ) :
    dynamicTerm a d 1 i = arithmeticTerm a d i := by
  simp [dynamicTerm, arithmeticTerm, dynamicStep]

/-- Zero scale collapses the sequence to its initial value. -/
@[simp] theorem dynamicTerm_zeroScale
    [Semiring C] (a d : C) (i : ℕ) :
    dynamicTerm a d 0 i = a := by
  simp [dynamicTerm, arithmeticTerm, dynamicStep]

/-- Zero difference collapses the sequence to its initial value. -/
@[simp] theorem dynamicTerm_zeroDiff
    [Semiring C] (a k : C) (i : ℕ) :
    dynamicTerm a 0 k i = a := by
  simp [dynamicTerm, arithmeticTerm, dynamicStep]

/-- Successive terms differ by the scaled common difference. -/
@[simp] theorem dynamicTerm_succ
    [Semiring C] (a d k : C) (i : ℕ) :
    dynamicTerm a d k (i + 1) = dynamicTerm a d k i + d * k := by
  simp [dynamicTerm, arithmeticTerm, dynamicStep, Nat.cast_add, add_mul, add_assoc]

/-! ## Small rational examples mirroring the Python demo without rounding -/

set_option linter.style.nativeDecide false in
example :
    dynamicSequence (1 : ℚ) 2 1 10 =
      [1, 3, 5, 7, 9, 11, 13, 15, 17, 19] := by
  native_decide

set_option linter.style.nativeDecide false in
example :
    dynamicSequence (3 : ℚ) 5 (102 / 100) 10 =
      [3, 81 / 10, 66 / 5, 183 / 10, 117 / 5,
        57 / 2, 168 / 5, 387 / 10, 219 / 5, 489 / 10] := by
  native_decide

end DHNT
end DkMath
