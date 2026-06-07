/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Sequence.Recurrence

#print "file: DkMath.Sequence.Arithmetic"

namespace DkMath
namespace Sequence

/-!
# Arithmetic sequence generators

Ordinary arithmetic sequences, dynamic arithmetic sequences, and variable
difference sequences all live here.  The dynamic arithmetic sequence is the
special case where the common difference is rescaled to `d * k`.
-/

variable {C : Type*}

/-- Ordinary arithmetic generator with origin `a` and common difference `d`. -/
def arithmeticGenerator [Semiring C] (a d : C) : AdditiveGenerator C where
  origin := a
  step := d

/-- The `k`-scaled common difference. -/
def dynamicStep [Mul C] (d k : C) : C :=
  d * k

/-- Dynamic arithmetic generator with common difference `d * k`. -/
def dynamicGenerator [Semiring C] (a d k : C) : AdditiveGenerator C :=
  arithmeticGenerator a (dynamicStep d k)

/-- The `i`-th term of an ordinary arithmetic sequence. -/
def arithmeticTerm [Semiring C] (a d : C) (i : ℕ) : C :=
  (arithmeticGenerator a d).term i

/-- The `i`-th term of a dynamic arithmetic sequence. -/
def dynamicTerm [Semiring C] (a d k : C) (i : ℕ) : C :=
  (dynamicGenerator a d k).term i

/-- The dynamic sequence as a finite list of its first `n` terms. -/
def dynamicSequence [Semiring C] (a d k : C) (n : ℕ) : List C :=
  (dynamicGenerator a d k).take n

/-- Dynamic arithmetic is ordinary arithmetic with common difference `d * k`. -/
@[simp] theorem dynamicTerm_eq_arithmeticTerm_scaledDiff
    [Semiring C] (a d k : C) (i : ℕ) :
    dynamicTerm a d k i = arithmeticTerm a (d * k) i := by
  rfl

/-- The `k = 1` specialization recovers the ordinary arithmetic sequence. -/
@[simp] theorem dynamicTerm_one
    [Semiring C] (a d : C) (i : ℕ) :
    dynamicTerm a d 1 i = arithmeticTerm a d i := by
  simp [dynamicTerm, arithmeticTerm, dynamicGenerator, arithmeticGenerator, dynamicStep,
    AdditiveGenerator.term]

/-- Zero scale collapses the sequence to its initial value. -/
@[simp] theorem dynamicTerm_zeroScale
    [Semiring C] (a d : C) (i : ℕ) :
    dynamicTerm a d 0 i = a := by
  simp [dynamicTerm, dynamicGenerator, arithmeticGenerator, dynamicStep,
    AdditiveGenerator.term]

/-- Zero difference collapses the sequence to its initial value. -/
@[simp] theorem dynamicTerm_zeroDiff
    [Semiring C] (a k : C) (i : ℕ) :
    dynamicTerm a 0 k i = a := by
  simp [dynamicTerm, dynamicGenerator, arithmeticGenerator, dynamicStep,
    AdditiveGenerator.term]

/-- Successive terms differ by the scaled common difference. -/
@[simp] theorem dynamicTerm_succ
    [Semiring C] (a d k : C) (i : ℕ) :
    dynamicTerm a d k (i + 1) = dynamicTerm a d k i + d * k := by
  exact AdditiveGenerator.term_succ (dynamicGenerator a d k) i

/-! ## Variable difference sequences -/

/-- A recurrence where the difference may depend on the index. -/
def variableDiffRecurrence [Add C] (a : C) (d : ℕ → C) : Recurrence C where
  seed := a
  next := fun i x => x + d i

/-- The `i`-th term of a variable-difference sequence. -/
def variableDiffTerm [Add C] (a : C) (d : ℕ → C) (i : ℕ) : C :=
  (variableDiffRecurrence a d).state i

@[simp] theorem variableDiffTerm_zero [Add C] (a : C) (d : ℕ → C) :
    variableDiffTerm a d 0 = a := by
  rfl

@[simp] theorem variableDiffTerm_succ [Add C] (a : C) (d : ℕ → C) (i : ℕ) :
    variableDiffTerm a d (i + 1) = variableDiffTerm a d i + d i := by
  rfl

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

set_option linter.style.nativeDecide false in
example :
    variableDiffTerm (0 : ℕ) (fun i => i + 1) 4 = 10 := by
  native_decide

end Sequence
end DkMath
