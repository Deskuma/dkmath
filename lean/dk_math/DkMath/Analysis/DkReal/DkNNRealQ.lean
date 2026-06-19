/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.DkReal.DkNNReal

#print "file: DkMath.Analysis.DkReal.DkNNRealQ"

/-!
# Quotient-backed nonnegative computable reals

`DkNNRealQ` identifies nonnegative interval approximations that have vanishing
separation. The operations below are lifted from `DkNNReal`, so the semiring
laws previously stated modulo representation equivalence become ordinary Lean
equalities.

This remains a computable representation layer. No evaluation into Mathlib's
`Real` is selected.
-/

namespace DkMath.Analysis

/-- Nonnegative computable real approximations modulo representation equivalence. -/
def DkNNRealQ :=
  Quotient DkNNReal.equivSetoid

namespace DkNNRealQ

/-- Quotient constructor from a nonnegative approximation. -/
def mk (x : DkNNReal) : DkNNRealQ :=
  Quotient.mk'' x

/-- Embed a nonnegative rational into the quotient. -/
def ofRat (q : ℚ) (hq : 0 ≤ q) : DkNNRealQ :=
  mk (DkNNReal.ofRat q hq)

/-- Quotient zero. -/
def zero : DkNNRealQ :=
  mk DkNNReal.zero

/-- Quotient one. -/
def one : DkNNRealQ :=
  mk DkNNReal.one

/-- Quotient addition. -/
def add (x y : DkNNRealQ) : DkNNRealQ :=
  Quotient.liftOn₂ x y
    (fun a b => mk (DkNNReal.add a b))
    (by
      intro a a' b b' haa' hbb'
      exact Quotient.sound (DkNNReal.equiv_add haa' hbb'))

/-- Quotient multiplication. -/
def mul (x y : DkNNRealQ) : DkNNRealQ :=
  Quotient.liftOn₂ x y
    (fun a b => mk (DkNNReal.mul a b))
    (by
      intro a a' b b' haa' hbb'
      exact Quotient.sound (DkNNReal.equiv_mul haa' hbb'))

/-- Quotient natural power. -/
def pow (x : DkNNRealQ) (d : ℕ) : DkNNRealQ :=
  Quotient.liftOn x
    (fun a => mk (DkNNReal.pow a d))
    (by
      intro a b hab
      exact Quotient.sound (DkNNReal.equiv_pow d hab))

instance : Zero DkNNRealQ where
  zero := zero

instance : One DkNNRealQ where
  one := one

instance : Add DkNNRealQ where
  add := add

instance : Mul DkNNRealQ where
  mul := mul

instance : Pow DkNNRealQ ℕ where
  pow := pow

/-- Quotient addition computes on representatives. -/
@[simp]
theorem mk_add (x y : DkNNReal) :
    mk (DkNNReal.add x y) = mk x + mk y := rfl

/-- Quotient multiplication computes on representatives. -/
@[simp]
theorem mk_mul (x y : DkNNReal) :
    mk (DkNNReal.mul x y) = mk x * mk y := rfl

/-- Quotient powers compute on representatives. -/
@[simp]
theorem mk_pow (x : DkNNReal) (d : ℕ) :
    mk (DkNNReal.pow x d) = mk x ^ d := rfl

/-!
## Exact rational rules
-/

/-- Quotient addition agrees with rational addition on embedded values. -/
theorem ofRat_add
    {p q : ℚ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    ofRat p hp + ofRat q hq = ofRat (p + q) (add_nonneg hp hq) :=
  Quotient.sound (DkNNReal.add_ofRat hp hq)

/-- Quotient multiplication agrees with rational multiplication on embedded values. -/
theorem ofRat_mul
    {p q : ℚ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    ofRat p hp * ofRat q hq = ofRat (p * q) (mul_nonneg hp hq) :=
  Quotient.sound (DkNNReal.mul_ofRat hp hq)

/-- Zeroth power is one in the quotient. -/
@[simp]
theorem pow_zero (x : DkNNRealQ) : x ^ (0 : ℕ) = 1 := by
  refine Quotient.inductionOn x ?_
  intro a
  exact Quotient.sound (DkNNReal.pow_zero a)

/-- First power is the original quotient value. -/
@[simp]
theorem pow_one (x : DkNNRealQ) : x ^ (1 : ℕ) = x := by
  refine Quotient.inductionOn x ?_
  intro a
  exact Quotient.sound (DkNNReal.pow_one a)

/-!
## Commutative semiring laws as quotient equalities

These theorems are intentionally provided before a full `Semiring` instance.
They validate the quotient design while keeping instance construction and
natural-number coercions as a separate API decision.
-/

theorem add_assoc (x y z : DkNNRealQ) :
    (x + y) + z = x + (y + z) := by
  refine Quotient.inductionOn₃ x y z ?_
  intro a b c
  exact Quotient.sound (DkNNReal.add_assoc a b c)

theorem add_comm (x y : DkNNRealQ) :
    x + y = y + x := by
  refine Quotient.inductionOn₂ x y ?_
  intro a b
  exact Quotient.sound (DkNNReal.add_comm a b)

@[simp]
theorem add_zero (x : DkNNRealQ) :
    x + 0 = x := by
  refine Quotient.inductionOn x ?_
  intro a
  exact Quotient.sound (DkNNReal.add_zero a)

@[simp]
theorem zero_add (x : DkNNRealQ) :
    0 + x = x := by
  refine Quotient.inductionOn x ?_
  intro a
  exact Quotient.sound (DkNNReal.zero_add a)

theorem mul_assoc (x y z : DkNNRealQ) :
    (x * y) * z = x * (y * z) := by
  refine Quotient.inductionOn₃ x y z ?_
  intro a b c
  exact Quotient.sound (DkNNReal.mul_assoc a b c)

theorem mul_comm (x y : DkNNRealQ) :
    x * y = y * x := by
  refine Quotient.inductionOn₂ x y ?_
  intro a b
  exact Quotient.sound (DkNNReal.mul_comm a b)

@[simp]
theorem mul_one (x : DkNNRealQ) :
    x * 1 = x := by
  refine Quotient.inductionOn x ?_
  intro a
  exact Quotient.sound (DkNNReal.mul_one a)

@[simp]
theorem one_mul (x : DkNNRealQ) :
    1 * x = x := by
  refine Quotient.inductionOn x ?_
  intro a
  exact Quotient.sound (DkNNReal.one_mul a)

@[simp]
theorem mul_zero (x : DkNNRealQ) :
    x * 0 = 0 := by
  refine Quotient.inductionOn x ?_
  intro a
  exact Quotient.sound (DkNNReal.mul_zero a)

@[simp]
theorem zero_mul (x : DkNNRealQ) :
    0 * x = 0 := by
  refine Quotient.inductionOn x ?_
  intro a
  exact Quotient.sound (DkNNReal.zero_mul a)

theorem left_distrib (x y z : DkNNRealQ) :
    x * (y + z) = x * y + x * z := by
  refine Quotient.inductionOn₃ x y z ?_
  intro a b c
  exact Quotient.sound (DkNNReal.left_distrib a b c)

theorem right_distrib (x y z : DkNNRealQ) :
    (x + y) * z = x * z + y * z := by
  refine Quotient.inductionOn₃ x y z ?_
  intro a b c
  exact Quotient.sound (DkNNReal.right_distrib a b c)

end DkNNRealQ

end DkMath.Analysis
