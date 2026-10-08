/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GNProductDegree
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.Ring

#print "file: DkMath.NumberTheory.GapFocusing.Focus"

/-!
# Gap focusing and its exact obstruction

The anchor is fixed in the coefficient ring and the gap is the formal variable
`X`. The remainder modulo `X` is exactly the difference of anchor powers.
The same equivalence does not hold for divisibility of evaluated elements.
The kernel is the existing `GTail d 1`, also called `GN`; no new kernel is defined.
-/

namespace DkMath.NumberTheory.GapFocusing

open DkMath.CosmicFormula Polynomial

variable {R : Type*} [CommRing R]

/-- Focusing is an invertible change of additive coordinates. -/
def focusCoordinates : (R × R) ≃ (R × R) where
  toFun ab := (ab.1 - ab.2, ab.2)
  invFun xu := (xu.1 + xu.2, xu.2)
  left_inv := by intro ab; ext <;> simp
  right_inv := by intro xu; ext <;> simp

/-- The constant obstruction relative to two chosen anchors. -/
def focusDefect (d : ℕ) (u v : R) : R := u ^ d - v ^ d

/-- Exact focused power difference over any commutative ring. -/
theorem focused_pow_sub (d : ℕ) (x u : R) :
    (x + u) ^ d - u ^ d = x * GTail d 1 x u := by
  rw [add_pow_eq_mul_GTail_one_add_gap, add_sub_cancel_right]

/-- The unfocused difference has an explicit constant remainder. -/
theorem unfocused_pow_sub (d : ℕ) (x u v : R) :
    (x + u) ^ d - v ^ d = x * GTail d 1 x u + focusDefect d u v := by
  rw [add_pow_eq_mul_GTail_one_add_gap]
  simp [focusDefect, add_sub_assoc]

/-- Evaluated divisibility only detects divisibility of the defect. -/
theorem gap_dvd_iff_dvd_defect (d : ℕ) (x u v : R) :
    x ∣ (x + u) ^ d - v ^ d ↔ x ∣ focusDefect d u v := by
  rw [unfocused_pow_sub]
  exact dvd_add_right (dvd_mul_right x (GTail d 1 x u))

/-- An anchor change has an additive cocycle, rather than invariant, behavior. -/
theorem focusDefect_cocycle (d : ℕ) (u v w : R) :
    focusDefect d u w = focusDefect d u v + focusDefect d v w := by
  simp only [focusDefect]
  ring

/-- Simultaneous scaling changes the defect by its degree. -/
theorem focusDefect_scale (d : ℕ) (c u v : R) :
    focusDefect d (c * u) (c * v) = c ^ d * focusDefect d u v := by
  simp only [focusDefect, mul_pow, mul_sub]

/-- The polynomial remainder is independent of any cancellation assumptions. -/
theorem unfocused_polynomial_remainder (d : ℕ) (u v : R) :
    (X + C u) ^ d - (C v) ^ d =
      X * GTail d 1 X (C u) + C (focusDefect d u v) := by
  simpa only [focusDefect, map_sub, map_pow] using
    unfocused_pow_sub d (X : R[X]) (C u) (C v)

/-- The exact zero-defect criterion concerns a formal gap, including `d = 0`. -/
theorem X_dvd_unfocused_iff (d : ℕ) (u v : R) :
    (X : R[X]) ∣ (X + C u) ^ d - (C v) ^ d ↔ u ^ d = v ^ d := by
  rw [X_dvd_iff, coeff_zero_eq_eval_zero]
  simp [sub_eq_zero]

/-- The chosen anchor uniquely determines the normalized polynomial quotient,
even over coefficient rings with zero divisors. -/
theorem focused_quotient_unique (d : ℕ) (u : R) (q : R[X]) :
    (X + C u) ^ d - (C u) ^ d = X * q ↔ q = GTail d 1 X (C u) := by
  rw [focused_pow_sub]
  constructor
  · intro h
    ext k
    have hk := congrArg (fun p : R[X] => p.coeff (k + 1)) h
    simpa using hk.symm
  · intro h
    rw [h]

/-- The remainder is the unique constant in any `X`-multiple decomposition. -/
theorem unfocused_constant_unique (d : ℕ) (u v r : R) (q : R[X])
    (h : (X + C u) ^ d - (C v) ^ d = X * q + C r) :
    r = focusDefect d u v := by
  have h0 := congrArg (fun p : R[X] => p.eval 0) h
  simpa [focusDefect] using h0.symm

/-- GN retains the first background coefficient after removing one gap. -/
theorem focused_quotient_eval_zero (d : ℕ) (u : R) :
    (GTail d 1 (X : R[X]) (C u)).eval 0 = (d : R) * u ^ (d - 1) := by
  rw [show (GTail d 1 (X : R[X]) (C u)).eval 0 = GTail d 1 0 u by
    simpa only [coe_evalRingHom, eval_X, eval_C] using
      map_GN (evalRingHom 0) d (X : R[X]) (C u)]
  simpa using GN_zero_eval d u

/-- A second formal gap factor is present exactly when the first background
coefficient vanishes. This includes characteristic-dependent multiplicity. -/
theorem X_sq_dvd_focused_iff (d : ℕ) (u : R) :
    (X : R[X]) ^ 2 ∣ (X + C u) ^ d - (C u) ^ d ↔
      (d : R) * u ^ (d - 1) = 0 := by
  rw [focused_pow_sub]
  have hcancel : (X : R[X]) ^ 2 ∣ X * GTail d 1 X (C u) ↔
      X ∣ GTail d 1 X (C u) := by
    constructor
    · rintro ⟨q, hq⟩
      refine ⟨q, ?_⟩
      ext k
      have hk := congrArg (fun p : R[X] => p.coeff (k + 1)) hq
      simpa [pow_two, mul_assoc] using hk
    · rintro ⟨q, hq⟩
      exact ⟨q, by rw [hq, pow_two, mul_assoc]⟩
  rw [hcancel, X_dvd_iff, coeff_zero_eq_eval_zero, focused_quotient_eval_zero]

end DkMath.NumberTheory.GapFocusing
