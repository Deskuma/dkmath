/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Sequence.Generator

#print "file: DkMath.Sequence.Recurrence"

namespace DkMath
namespace Sequence

/-!
# Recurrence generators

Recurrences model sequences whose next value depends on the current index and
state.  `StateRecurrence` adds an observation map, which is the natural home for
Fibonacci-style two-register dynamics.
-/

/-- A first-order recurrence on values of type `A`. -/
structure Recurrence (A : Type*) where
  seed : A
  next : ℕ → A → A

namespace Recurrence

/-- The state after `n` recurrence steps. -/
def state (r : Recurrence A) : ℕ → A
  | 0 => r.seed
  | n + 1 => r.next n (state r n)

/-- A recurrence viewed as a closed-form sequence by iteration. -/
def toClosed (r : Recurrence A) : Closed A where
  term := r.state

/-- The first `n` states. -/
def take (r : Recurrence A) (n : ℕ) : List A :=
  r.toClosed.take n

@[simp] theorem state_zero (r : Recurrence A) :
    r.state 0 = r.seed := by
  rfl

@[simp] theorem state_succ (r : Recurrence A) (n : ℕ) :
    r.state (n + 1) = r.next n (r.state n) := by
  rfl

end Recurrence

/-- A recurrence on hidden states, together with an observation map. -/
structure StateRecurrence (S A : Type*) where
  seed : S
  next : ℕ → S → S
  observe : S → A

namespace StateRecurrence

/-- The hidden state after `n` steps. -/
def state (r : StateRecurrence S A) : ℕ → S
  | 0 => r.seed
  | n + 1 => r.next n (state r n)

/-- The observed `n`-th term. -/
def term (r : StateRecurrence S A) (n : ℕ) : A :=
  r.observe (r.state n)

/-- Forget a state recurrence to its observed closed-form sequence. -/
def toClosed (r : StateRecurrence S A) : Closed A where
  term := r.term

/-- The first `n` observed terms. -/
def take (r : StateRecurrence S A) (n : ℕ) : List A :=
  r.toClosed.take n

@[simp] theorem state_zero (r : StateRecurrence S A) :
    r.state 0 = r.seed := by
  rfl

@[simp] theorem state_succ (r : StateRecurrence S A) (n : ℕ) :
    r.state (n + 1) = r.next n (r.state n) := by
  rfl

@[simp] theorem term_zero (r : StateRecurrence S A) :
    r.term 0 = r.observe r.seed := by
  rfl

end StateRecurrence

end Sequence
end DkMath
