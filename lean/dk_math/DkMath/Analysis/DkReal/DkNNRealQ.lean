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

/-- Canonical natural-number embedding through nonnegative rationals. -/
def natCast (n : ℕ) : DkNNRealQ :=
  ofRat (n : ℚ) (by positivity)

instance : NatCast DkNNRealQ where
  natCast := natCast

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

/-- Natural-number casts are the corresponding embedded rationals. -/
@[simp]
theorem natCast_eq_ofRat (n : ℕ) :
    (n : DkNNRealQ) = ofRat (n : ℚ) (by positivity) := rfl

/-- The natural cast of zero is quotient zero. -/
@[simp]
theorem natCast_zero : ((0 : ℕ) : DkNNRealQ) = 0 := by
  rfl

/-- Natural casts preserve successor. -/
theorem natCast_succ (n : ℕ) :
    ((n + 1 : ℕ) : DkNNRealQ) = (n : DkNNRealQ) + 1 := by
  simpa only [natCast_eq_ofRat, Nat.cast_add, Nat.cast_one] using
    (ofRat_add (show 0 ≤ (n : ℚ) by positivity) zero_le_one).symm

/-- Natural casts preserve addition. -/
theorem natCast_add (m n : ℕ) :
    ((m + n : ℕ) : DkNNRealQ) = (m : DkNNRealQ) + (n : DkNNRealQ) := by
  simpa only [natCast_eq_ofRat, Nat.cast_add] using
    (ofRat_add
      (show 0 ≤ (m : ℚ) by positivity)
      (show 0 ≤ (n : ℚ) by positivity)).symm

/-- Natural casts preserve multiplication. -/
theorem natCast_mul (m n : ℕ) :
    ((m * n : ℕ) : DkNNRealQ) = (m : DkNNRealQ) * (n : DkNNRealQ) := by
  simpa only [natCast_eq_ofRat, Nat.cast_mul] using
    (ofRat_mul
      (show 0 ≤ (m : ℚ) by positivity)
      (show 0 ≤ (n : ℚ) by positivity)).symm

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

/-!
## Commutative semiring instance

The natural cast is fixed to the rational singleton embedding. The standard
algebraic hierarchy can therefore use the quotient equalities proved above.
-/

instance : CommSemiring DkNNRealQ where
  add_assoc := add_assoc
  zero_add := zero_add
  add_zero := add_zero
  add_comm := add_comm
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  left_distrib := left_distrib
  right_distrib := right_distrib
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_comm := mul_comm
  natCast := natCast
  natCast_zero := natCast_zero
  natCast_succ := natCast_succ
  nsmul := nsmulRec
  nsmul_zero := by intros; rfl
  nsmul_succ := by intros; rfl

end DkNNRealQ

end DkMath.Analysis
