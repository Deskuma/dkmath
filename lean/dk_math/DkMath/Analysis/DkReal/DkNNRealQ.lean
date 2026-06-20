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

The resulting quotient is a commutative semiring. Its natural-number embedding
sends `n` to the class of the constant singleton interval `[n,n]`.

This remains a computable representation layer. Quotient elimination is used
only to define representation-independent operations; no evaluation into
Mathlib's `Real` is selected.

`DkReal.Order` defines an asymptotic representative order, proves invariance
under `DkNNReal.Equiv`, and installs a `PartialOrder` on this quotient.

Addition, multiplication, and natural powers are monotone for the asymptotic
order. Prove that zero is least and verify the intended ordered-algebra
hierarchy before installing stronger typeclasses.

[TODO] A semantic map to Mathlib's `NNReal` should be placed in a separate
bridge module and proved to preserve zero, one, addition, multiplication,
natural powers, and the future order.
-/

namespace DkMath.Analysis

/--
Nonnegative computable real approximations modulo vanishing separation.

Two representatives define the same quotient value precisely when the
separation of their stagewise rational intervals tends to zero.
-/
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

/-- Additive identity induced by the class of the singleton interval `[0,0]`. -/
instance : Zero DkNNRealQ where
  zero := zero

/-- Multiplicative identity induced by the class of the singleton interval `[1,1]`. -/
instance : One DkNNRealQ where
  one := one

/-- Addition induced by stagewise Minkowski addition of representatives. -/
instance : Add DkNNRealQ where
  add := add

/-- Multiplication induced by endpoint multiplication of nonnegative representatives. -/
instance : Mul DkNNRealQ where
  mul := mul

/-- Natural powers induced by stagewise nonnegative endpoint powers. -/
instance : Pow DkNNRealQ ℕ where
  pow := pow

/-- Canonical natural-number embedding through nonnegative rationals. -/
def natCast (n : ℕ) : DkNNRealQ :=
  ofRat (n : ℚ) (by positivity)

/-- Natural-number cast through constant nonnegative rational intervals. -/
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

/-- Successor powers agree with multiplication by the base. -/
theorem pow_succ_eq (x : DkNNRealQ) (d : ℕ) :
    x ^ (d + 1) = x ^ d * x := by
  refine Quotient.inductionOn x ?_
  intro a
  exact Quotient.sound (DkNNReal.pow_succ a d)

/-!
## Commutative semiring laws as quotient equalities

These theorems are intentionally provided before a full `Semiring` instance.
They validate the quotient design while keeping instance construction and
natural-number coercions as a separate API decision.
-/

/-- Quotient addition is associative. -/
theorem add_assoc (x y z : DkNNRealQ) :
    (x + y) + z = x + (y + z) := by
  refine Quotient.inductionOn₃ x y z ?_
  intro a b c
  exact Quotient.sound (DkNNReal.add_assoc a b c)

/-- Quotient addition is commutative. -/
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

/-- Quotient multiplication is associative. -/
theorem mul_assoc (x y z : DkNNRealQ) :
    (x * y) * z = x * (y * z) := by
  refine Quotient.inductionOn₃ x y z ?_
  intro a b c
  exact Quotient.sound (DkNNReal.mul_assoc a b c)

/-- Quotient multiplication is commutative. -/
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

/-- Multiplication distributes over quotient addition from the left. -/
theorem left_distrib (x y z : DkNNRealQ) :
    x * (y + z) = x * y + x * z := by
  refine Quotient.inductionOn₃ x y z ?_
  intro a b c
  exact Quotient.sound (DkNNReal.left_distrib a b c)

/-- Multiplication distributes over quotient addition from the right. -/
theorem right_distrib (x y z : DkNNRealQ) :
    (x + y) * z = x * z + y * z := by
  refine Quotient.inductionOn₃ x y z ?_
  intro a b c
  exact Quotient.sound (DkNNReal.right_distrib a b c)

/-!
## Commutative semiring instance

The natural cast is fixed to the rational singleton embedding. The standard
algebraic hierarchy can therefore use the quotient equalities proved above.
The instance does not assert completeness, decidable equality, linear order,
or equivalence with all of Mathlib's nonnegative real numbers.
-/

/--
Commutative semiring structure on nonnegative computable-real values.

The structure is extensional because its carrier is already quotiented by
vanishing interval separation. It supplies algebraic operations only; no order,
topology, metric completeness, or semantic equivalence with `NNReal` is
asserted.
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
