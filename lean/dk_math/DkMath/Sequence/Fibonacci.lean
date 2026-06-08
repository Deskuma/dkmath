/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Sequence.Arithmetic

#print "file: DkMath.Sequence.Fibonacci"

namespace DkMath
namespace Sequence

/-!
# Fibonacci as a state recurrence

Fibonacci is represented by the two-register state `(F n, F (n+1))`.
-/

/-- The Fibonacci state recurrence. -/
def fibonacciState : StateRecurrence (ℕ × ℕ) ℕ where
  seed := (0, 1)
  next := fun _ s => (s.2, s.1 + s.2)
  observe := Prod.fst

/-- Fibonacci term obtained by observing `fibonacciState`. -/
def fibonacciTerm (n : ℕ) : ℕ :=
  fibonacciState.term n

/-- First `n` Fibonacci terms. -/
def fibonacciSequence (n : ℕ) : List ℕ :=
  fibonacciState.take n

@[simp] theorem fibonacciTerm_zero :
    fibonacciTerm 0 = 0 := by
  rfl

@[simp] theorem fibonacciTerm_one :
    fibonacciTerm 1 = 1 := by
  rfl

set_option linter.style.nativeDecide false in
@[simp] theorem fibonacciSequence_seven :
    fibonacciSequence 7 = [0, 1, 1, 2, 3, 5, 8] := by
  native_decide

end Sequence
end DkMath
