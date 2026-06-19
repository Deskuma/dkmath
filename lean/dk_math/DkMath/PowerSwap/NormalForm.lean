/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- PowerSwap module: power normal forms

import DkMath.PowerSwap.Exchange

#print "file: DkMath.PowerSwap.NormalForm"

namespace DkMath
namespace PowerSwap

/-!
# Power normal forms

This file packages the expression `z ^ n` as a small normal-form object.
It is the first bridge from product-shaped expressions toward a power-axis
universe.
-/

/-- A natural-number power normal form `base ^ exponent`. -/
structure PowNormalForm where
  base : ℕ
  exponent : ℕ
deriving DecidableEq, Repr

namespace PowNormalForm

/-- Evaluate a power normal form back to `ℕ`. -/
def eval (p : PowNormalForm) : ℕ :=
  p.base ^ p.exponent

/-- Build a normal form directly from a base and exponent. -/
def ofPow (base exponent : ℕ) : PowNormalForm where
  base := base
  exponent := exponent

/-- Raising a normal form to `m` multiplies its exponent by `m`. -/
def power (p : PowNormalForm) (m : ℕ) : PowNormalForm where
  base := p.base
  exponent := p.exponent * m

/-- Product of two normal forms sharing one base. -/
def mulSameBase (p q : PowNormalForm) (_h : p.base = q.base) : PowNormalForm where
  base := p.base
  exponent := p.exponent + q.exponent

@[simp] theorem eval_ofPow (base exponent : ℕ) :
    (ofPow base exponent).eval = base ^ exponent := by
  rfl

@[simp] theorem eval_power (p : PowNormalForm) (m : ℕ) :
    (p.power m).eval = p.eval ^ m := by
  cases p
  simp [power, eval, pow_mul]

@[simp] theorem eval_mulSameBase
    (p q : PowNormalForm) (h : p.base = q.base) :
    (p.mulSameBase q h).eval = p.eval * q.eval := by
  cases p with
  | mk pb pe =>
    cases q with
    | mk qb qe =>
      dsimp [mulSameBase, eval] at h ⊢
      subst qb
      rw [pow_add]

end PowNormalForm

/-- A value `n` equipped with a power normal form that evaluates to it. -/
structure HasPowNormalForm (n : ℕ) where
  form : PowNormalForm
  eval_eq : form.eval = n

namespace HasPowNormalForm

/-- Every explicit power has its corresponding normal form. -/
def ofPow (base exponent : ℕ) : HasPowNormalForm (base ^ exponent) where
  form := PowNormalForm.ofPow base exponent
  eval_eq := by simp [PowNormalForm.eval, PowNormalForm.ofPow]

/-- Raise a normalized value to a power by multiplying the exponent. -/
def power {n : ℕ} (h : HasPowNormalForm n) (m : ℕ) :
    HasPowNormalForm (n ^ m) where
  form := h.form.power m
  eval_eq := by
    calc
      (h.form.power m).eval = h.form.eval ^ m := PowNormalForm.eval_power h.form m
      _ = n ^ m := by rw [h.eval_eq]

/-- Product of two normalized values with the same normal-form base. -/
def mulSameBase {n m : ℕ}
    (hn : HasPowNormalForm n) (hm : HasPowNormalForm m)
    (hbase : hn.form.base = hm.form.base) :
    HasPowNormalForm (n * m) where
  form := hn.form.mulSameBase hm.form hbase
  eval_eq := by
    calc
      (hn.form.mulSameBase hm.form hbase).eval = hn.form.eval * hm.form.eval :=
        PowNormalForm.eval_mulSameBase hn.form hm.form hbase
      _ = n * m := by rw [hn.eval_eq, hm.eval_eq]

end HasPowNormalForm

/-! ## Exchange bridge -/

/--
If `A = a ^ t`, then `A ^ m` has normal form `a ^ (t * m)`.

This is the normal-form packaging of `exchange_condition_minimal_nat`.
-/
def normalForm_power_of_eq_pow
    (a A t m : ℕ) (hA : A = a ^ t) :
    HasPowNormalForm (A ^ m) where
  form := PowNormalForm.ofPow a (t * m)
  eval_eq := by
    calc
      (PowNormalForm.ofPow a (t * m)).eval = a ^ (t * m) :=
        PowNormalForm.eval_ofPow a (t * m)
      _ = A ^ m := (exchange_condition_minimal_nat a A t m hA).symm

/--
Expression-level form of `normalForm_power_of_eq_pow`.
-/
theorem eval_normalForm_power_of_eq_pow
    (a A t m : ℕ) (hA : A = a ^ t) :
    (normalForm_power_of_eq_pow a A t m hA).form.eval = A ^ m :=
  (normalForm_power_of_eq_pow a A t m hA).eval_eq

/-! ## Small examples -/

example :
    (normalForm_power_of_eq_pow 2 4 2 2 (by norm_num)).form
      = PowNormalForm.ofPow 2 4 := by
  rfl

example :
    (normalForm_power_of_eq_pow 3 27 3 2 (by norm_num)).form.eval = 729 := by
  norm_num [normalForm_power_of_eq_pow, PowNormalForm.eval, PowNormalForm.ofPow]

end PowerSwap
end DkMath
