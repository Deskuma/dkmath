/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GTail
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Product-degree composition of the gap-normalized kernel

The identity holds over every commutative semiring, including zero gaps and
zero divisors. The proof first establishes a universal polynomial identity
over natural coefficients, then evaluates it. Cancellation is confined to
the formal variable; no cancellation hypothesis is imposed on the target.
-/

namespace DkMath.CosmicFormula

/-- Semiring homomorphisms preserve the existing gap-normalized tail. -/
theorem map_GN {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (d : ℕ) (x u : R) :
    f (GTail d 1 x u) = GTail d 1 (f x) (f u) := by
  simp only [GTail, map_sum, map_mul, map_pow, map_natCast]

private theorem GN_mul_degree_polynomial (a b : ℕ) :
    let x : MvPolynomial (Fin 2) ℕ := MvPolynomial.X 0
    let u : MvPolynomial (Fin 2) ℕ := MvPolynomial.X 1
    GTail (a * b) 1 x u =
      GTail a 1 x u * GTail b 1 (x * GTail a 1 x u) (u ^ a) := by
  dsimp only
  let x : MvPolynomial (Fin 2) ℕ := MvPolynomial.X 0
  let u : MvPolynomial (Fin 2) ℕ := MvPolynomial.X 1
  have ha := add_pow_eq_mul_GTail_one_add_gap a x u
  have hb := add_pow_eq_mul_GTail_one_add_gap b (x * GTail a 1 x u) (u ^ a)
  have hab := add_pow_eq_mul_GTail_one_add_gap (a * b) x u
  have hsum : x * GTail (a * b) 1 x u + u ^ (a * b) =
      x * (GTail a 1 x u * GTail b 1 (x * GTail a 1 x u) (u ^ a)) +
        u ^ (a * b) := by
    calc
      _ = (x + u) ^ (a * b) := hab.symm
      _ = ((x + u) ^ a) ^ b := pow_mul _ _ _
      _ = (x * GTail a 1 x u + u ^ a) ^ b := by rw [ha]
      _ = _ := by rw [hb, ← pow_mul, mul_assoc]
  exact mul_left_cancel₀ (MvPolynomial.X_ne_zero (R := ℕ) 0)
    (add_right_cancel hsum)

/-- Cancellation-free product-degree composition, valid also at `x = 0`.
The `GN` kernel is the existing `r = 1` tail, with no new definition. -/
theorem GN_mul_degree {R : Type*} [CommSemiring R]
    (a b : ℕ) (x u : R) :
    GTail (a * b) 1 x u =
      GTail a 1 x u * GTail b 1 (x * GTail a 1 x u) (u ^ a) := by
  let f : MvPolynomial (Fin 2) ℕ →+* R :=
    MvPolynomial.eval₂Hom (Nat.castRingHom R) (fun i => if i = 0 then x else u)
  have h := congrArg f (GN_mul_degree_polynomial a b)
  simpa only [map_GN, map_mul, map_pow, f, MvPolynomial.eval₂Hom_X',
    ite_eq_right (show (1 : Fin 2) ≠ 0 by decide), ↓reduceIte] using h

end DkMath.CosmicFormula
