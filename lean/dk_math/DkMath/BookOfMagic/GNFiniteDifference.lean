/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.CosmicFormulaBinom
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Tactic

namespace DkMath.BookOfMagic

open scoped BigOperators

/-- The coefficient-weighted GN finite difference associated to a polynomial. -/
def GNFiniteDifference
    {R : Type*}
    [CommSemiring R]
    (p : Polynomial R)
    (h t : R) : R :=
  p.sum fun n a ↦ a * DkMath.CosmicFormulaBinom.GN n h t

/-- The GN finite difference as an explicit sum over polynomial support. -/
theorem GNFiniteDifference_eq_support_sum
    {R : Type*}
    [CommSemiring R]
    (p : Polynomial R)
    (h t : R) :
    GNFiniteDifference p h t =
      ∑ n ∈ p.support,
        p.coeff n * DkMath.CosmicFormulaBinom.GN n h t := by
  rfl

@[simp]
theorem GNFiniteDifference_zero
    {R : Type*}
    [CommSemiring R]
    (h t : R) :
    GNFiniteDifference (0 : Polynomial R) h t = 0 := by
  simp [GNFiniteDifference]

theorem GNFiniteDifference_add
    {R : Type*}
    [CommSemiring R]
    (p q : Polynomial R)
    (h t : R) :
    GNFiniteDifference (p + q) h t =
      GNFiniteDifference p h t + GNFiniteDifference q h t := by
  apply Polynomial.sum_add_index
  · intro n
    simp
  · intro n a b
    simp [add_mul]

@[simp]
theorem GNFiniteDifference_monomial
    {R : Type*}
    [CommSemiring R]
    (n : ℕ)
    (a h t : R) :
    GNFiniteDifference (Polynomial.monomial n a) h t =
      a * DkMath.CosmicFormulaBinom.GN n h t := by
  simp [GNFiniteDifference]

@[simp]
theorem GNFiniteDifference_C
    {R : Type*}
    [CommSemiring R]
    (a h t : R) :
    GNFiniteDifference (Polynomial.C a) h t = 0 := by
  simp [GNFiniteDifference, DkMath.CosmicFormulaBinom.GN]

/-- Polynomial finite differences factor through the GN coefficient sum. -/
theorem eval_add_sub_eval_eq_mul_GNFiniteDifference
    {R : Type*}
    [CommRing R]
    (p : Polynomial R)
    (h t : R) :
    p.eval (t + h) - p.eval t =
      h * GNFiniteDifference p h t := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.eval_add, Polynomial.eval_add,
        GNFiniteDifference_add]
      calc
        p.eval (t + h) + q.eval (t + h) - (p.eval t + q.eval t) =
            (p.eval (t + h) - p.eval t) +
              (q.eval (t + h) - q.eval t) := by ring
        _ = h * GNFiniteDifference p h t +
              h * GNFiniteDifference q h t := by rw [hp, hq]
        _ = h * (GNFiniteDifference p h t +
              GNFiniteDifference q h t) := by ring
  | monomial n a =>
      simp only [Polynomial.eval_monomial, GNFiniteDifference_monomial]
      have hGN :=
        DkMath.CosmicFormulaBinom.cosmic_id_csr' (R := R) n h t
      rw [show t + h = h + t by ac_rfl, hGN]
      ring

/-- Away from zero increment, the polynomial difference quotient is its GN sum. -/
theorem differenceQuotient_eq_GNFiniteDifference
    {K : Type*}
    [Field K]
    (p : Polynomial K)
    (h t : K)
    (hh : h ≠ 0) :
    (p.eval (t + h) - p.eval t) / h =
      GNFiniteDifference p h t := by
  rw [eval_add_sub_eval_eq_mul_GNFiniteDifference]
  simp [hh]

/-- The cubic monomial instance of the GN finite-difference identity. -/
example {R : Type*} [CommRing R] (h t : R) :
    Polynomial.eval (t + h) (Polynomial.X ^ 3) -
        Polynomial.eval t (Polynomial.X ^ 3) =
      h * DkMath.CosmicFormulaBinom.GN 3 h t := by
  rw [Polynomial.X_pow_eq_monomial]
  simpa only [GNFiniteDifference_monomial, one_mul] using
    (eval_add_sub_eval_eq_mul_GNFiniteDifference
      (p := Polynomial.monomial 3 (1 : R)) h t)

end DkMath.BookOfMagic
