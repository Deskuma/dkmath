/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.DkReal.Equiv

#print "file: DkMath.Analysis.DkReal.DkNNReal"

/-!
# Nonnegative DkReal wrapper

`DkNNReal` packages a `DkReal` approximation together with stagewise
nonnegativity. It removes proof arguments from the public nonnegative
arithmetic operations while retaining the computable interval representation.

Algebraic laws are stated using representation equivalence, not raw structure
equality. A quotient can be introduced later once its public API is justified.
-/

namespace DkMath.Analysis

/-- A nonnegative computable real approximation. -/
structure DkNNReal where
  val : DkReal
  nonnegative : DkReal.Nonnegative val

namespace DkNNReal

/-- Embed a nonnegative rational as a constant singleton approximation. -/
def ofRat (q : ℚ) (hq : 0 ≤ q) : DkNNReal :=
  ⟨DkReal.ofRat q, DkReal.nonnegative_ofRat hq⟩

/-- The nonnegative zero approximation. -/
def zero : DkNNReal :=
  ofRat 0 le_rfl

/-- The nonnegative one approximation. -/
def one : DkNNReal :=
  ofRat 1 zero_le_one

/-- Addition of nonnegative approximations. -/
def add (x y : DkNNReal) : DkNNReal :=
  ⟨DkReal.add x.val y.val, DkReal.nonnegative_add x.nonnegative y.nonnegative⟩

/-- Multiplication of nonnegative approximations. -/
def mul (x y : DkNNReal) : DkNNReal :=
  ⟨DkReal.mulNonneg x.val y.val x.nonnegative y.nonnegative,
    DkReal.nonnegative_mulNonneg x.nonnegative y.nonnegative⟩

/-- Natural power of a nonnegative approximation. -/
def pow (x : DkNNReal) (d : ℕ) : DkNNReal :=
  ⟨DkReal.powNonneg d x.val x.nonnegative,
    DkReal.nonnegative_powNonneg d x.nonnegative⟩

/-- Wrapper equivalence induced by `DkReal.Equiv`. -/
def Equiv (x y : DkNNReal) : Prop :=
  DkReal.Equiv x.val y.val

/-- Wrapper equivalence is reflexive. -/
theorem equiv_refl (x : DkNNReal) : Equiv x x :=
  DkReal.equiv_refl x.val

/-- Wrapper equivalence is symmetric. -/
theorem equiv_symm {x y : DkNNReal} (hxy : Equiv x y) : Equiv y x :=
  DkReal.equiv_symm hxy

/-- Wrapper equivalence is transitive. -/
theorem equiv_trans
    {x y z : DkNNReal} (hxy : Equiv x y) (hyz : Equiv y z) :
    Equiv x z :=
  DkReal.equiv_trans hxy hyz

/-- Setoid of nonnegative approximation representations. -/
def equivSetoid : Setoid DkNNReal where
  r := Equiv
  iseqv := ⟨equiv_refl, @equiv_symm, @equiv_trans⟩

/-!
## Arithmetic congruence

The wrapper operations respect representation equivalence because their
underlying `DkReal` operations do.
-/

/-- Addition respects wrapper equivalence. -/
theorem equiv_add
    {x x' y y' : DkNNReal} (hxx' : Equiv x x') (hyy' : Equiv y y') :
    Equiv (add x y) (add x' y') :=
  DkReal.equiv_add hxx' hyy'

/-- Multiplication respects wrapper equivalence. -/
theorem equiv_mul
    {x x' y y' : DkNNReal} (hxx' : Equiv x x') (hyy' : Equiv y y') :
    Equiv (mul x y) (mul x' y') :=
  DkReal.equiv_mulNonneg
    x.nonnegative x'.nonnegative y.nonnegative y'.nonnegative hxx' hyy'

/-- Natural powers respect wrapper equivalence. -/
theorem equiv_pow
    (d : ℕ) {x y : DkNNReal} (hxy : Equiv x y) :
    Equiv (pow x d) (pow y d) :=
  DkReal.equiv_powNonneg d x.nonnegative y.nonnegative hxy

/-!
## Nonnegative semiring laws modulo representation equivalence

These are the algebraic laws needed by a future quotient. They intentionally
use `Equiv`; raw equality would distinguish different interval sequences
representing the same value.
-/

/-- Addition is associative modulo representation equivalence. -/
theorem add_assoc (x y z : DkNNReal) :
    Equiv (add (add x y) z) (add x (add y z)) :=
  DkReal.equiv_of_interval_eq (DkReal.add_assoc_interval x.val y.val z.val)

/-- Addition is commutative modulo representation equivalence. -/
theorem add_comm (x y : DkNNReal) :
    Equiv (add x y) (add y x) :=
  DkReal.equiv_of_interval_eq (DkReal.add_comm_interval x.val y.val)

/-- Zero is a right additive identity modulo representation equivalence. -/
theorem add_zero (x : DkNNReal) :
    Equiv (add x zero) x :=
  DkReal.equiv_of_interval_eq (DkReal.add_zero_interval x.val)

/-- Zero is a left additive identity modulo representation equivalence. -/
theorem zero_add (x : DkNNReal) :
    Equiv (add zero x) x :=
  DkReal.equiv_of_interval_eq (DkReal.zero_add_interval x.val)

/-- Multiplication is associative modulo representation equivalence. -/
theorem mul_assoc (x y z : DkNNReal) :
    Equiv (mul (mul x y) z) (mul x (mul y z)) :=
  DkReal.equiv_of_interval_eq
    (DkReal.mulNonneg_assoc_interval
      x.val y.val z.val x.nonnegative y.nonnegative z.nonnegative)

/-- Multiplication is commutative modulo representation equivalence. -/
theorem mul_comm (x y : DkNNReal) :
    Equiv (mul x y) (mul y x) :=
  DkReal.equiv_of_interval_eq
    (DkReal.mulNonneg_comm_interval
      x.val y.val x.nonnegative y.nonnegative)

/-- One is a right multiplicative identity modulo representation equivalence. -/
theorem mul_one (x : DkNNReal) :
    Equiv (mul x one) x :=
  DkReal.equiv_of_interval_eq
    (DkReal.mulNonneg_one_interval x.val x.nonnegative)

/-- One is a left multiplicative identity modulo representation equivalence. -/
theorem one_mul (x : DkNNReal) :
    Equiv (mul one x) x :=
  DkReal.equiv_of_interval_eq
    (DkReal.one_mulNonneg_interval x.val x.nonnegative)

/-- Multiplication distributes over addition from the left modulo equivalence. -/
theorem left_distrib (x y z : DkNNReal) :
    Equiv (mul x (add y z)) (add (mul x y) (mul x z)) :=
  DkReal.equiv_of_interval_eq
    (DkReal.left_distrib_interval
      x.val y.val z.val x.nonnegative y.nonnegative z.nonnegative)

/-- Multiplication distributes over addition from the right modulo equivalence. -/
theorem right_distrib (x y z : DkNNReal) :
    Equiv (mul (add x y) z) (add (mul x z) (mul y z)) :=
  DkReal.equiv_of_interval_eq
    (DkReal.right_distrib_interval
      x.val y.val z.val x.nonnegative y.nonnegative z.nonnegative)

end DkNNReal

end DkMath.Analysis
