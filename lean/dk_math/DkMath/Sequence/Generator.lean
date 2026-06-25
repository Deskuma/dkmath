/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

#print "file: DkMath.Sequence.Generator"

namespace DkMath
namespace Sequence

/-!
# Sequence generators

This file contains the small, KUS-independent core for sequence-like objects:

* a closed-form sequence `Closed`,
* an additive generator `origin + i * step`.
-/

/-- A closed-form sequence is just a term function `ℕ → A`. -/
structure Closed (A : Type*) where
  term : ℕ → A

namespace Closed

/-- The first `n` terms of a closed-form sequence. -/
def take {A} (s : Closed A) (n : ℕ) : List A :=
  (List.range n).map s.term

@[simp] theorem take_zero {A} (s : Closed A) :
    s.take 0 = [] := by
  rfl

end Closed

/--
An additive generator packages the principle
`term i = origin + i * step`.

This is the abstract core behind ordinary and dynamic arithmetic sequences.
-/
structure AdditiveGenerator (C : Type*) [Semiring C] where
  origin : C
  step : C

namespace AdditiveGenerator

variable {C : Type*} [Semiring C]

/-- The `i`-th term generated from `origin` by repeated `step`. -/
def term (g : AdditiveGenerator C) (i : ℕ) : C :=
  g.origin + (i : C) * g.step

/-- The first `n` generated terms. -/
def take (g : AdditiveGenerator C) (n : ℕ) : List C :=
  (List.range n).map g.term

/-- Forget an additive generator to its closed-form term function. -/
def toClosed (g : AdditiveGenerator C) : Closed C where
  term := g.term

/-- Rescale the step while keeping the origin fixed. -/
def rescale (g : AdditiveGenerator C) (k : C) : AdditiveGenerator C where
  origin := g.origin
  step := g.step * k

@[simp] theorem term_zero (g : AdditiveGenerator C) :
    g.term 0 = g.origin := by
  simp [term]

@[simp] theorem term_succ (g : AdditiveGenerator C) (i : ℕ) :
    g.term (i + 1) = g.term i + g.step := by
  simp [term, Nat.cast_add, add_mul, add_assoc]

@[simp] theorem take_zero (g : AdditiveGenerator C) :
    g.take 0 = [] := by
  rfl

@[simp] theorem toClosed_term (g : AdditiveGenerator C) (i : ℕ) :
    g.toClosed.term i = g.term i := by
  rfl

@[simp] theorem rescale_term (g : AdditiveGenerator C) (k : C) (i : ℕ) :
    (g.rescale k).term i = g.origin + (i : C) * (g.step * k) := by
  rfl

end AdditiveGenerator

end Sequence
end DkMath
