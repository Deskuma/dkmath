/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.CosmicFormulaBinom
import DkMath.NumberTheory.TraceOneQuadratic

#print "file: DkMath.NumberTheory.GNThreeQuadratic"

open scoped BigOperators

namespace DkMath.NumberTheory

open DkMath.CosmicFormulaBinom
open DkMath.NumberTheory.TraceOneQuadratic

/-!
## The degree-three GN quadratic shell

This file studies the dual-oriented kernel `GN 3 u x`.  It is the positive
definite quadratic form

`u^2 + 3*u*x + 3*x^2 = (x + u)^2 + (x + u)*x + x^2`,

and its integral completed-square form is

`4 * GN 3 u x = u^2 + 3 * (2*x + u)^2`.

The representation of a prime target here is additive/polynomial coordinate
data, not a multiplicative factorization of that prime.  No classification of
the represented primes is asserted.  For a positive prime-target
representation of degree `3`, GNPC-004 supplies the independent residue filter
`3 ∣ p - 1`; this file adds the stronger coordinate shell
`4 * p = u ^ 2 + 3 * (2 * x + u) ^ 2`.
-/

/-- The cubic GN kernel in the dual coordinate orientation. -/
theorem GN_three_dual_explicit (u x : ℕ) :
    DkMath.CosmicFormulaBinom.GN 3 u x =
      u ^ 2 + 3 * u * x + 3 * x ^ 2 := by
  rw [GN_eq_sum]
  norm_num [Finset.sum_range_succ']

/-- The same cubic value as the positive-definite discriminant `-3` form. -/
theorem GN_three_eq_discriminant_neg_three_form (u x : ℕ) :
    DkMath.CosmicFormulaBinom.GN 3 u x =
      (x + u) ^ 2 + (x + u) * x + x ^ 2 := by
  rw [GN_three_dual_explicit]
  ring

/-- The cubic GN value as an integral `s = -1` trace-one norm. -/
theorem GN_three_eq_traceOneNorm_negOne (u x : ℕ) :
    ((DkMath.CosmicFormulaBinom.GN 3 u x : ℕ) : ℤ) =
      DkMath.NumberTheory.TraceOneQuadratic.norm
        (⟨((x + u : ℕ) : ℤ), (x : ℤ)⟩ :
          DkMath.NumberTheory.TraceOneQuadratic.TraceOneInt (-1)) := by
  rw [GN_three_eq_discriminant_neg_three_form]
  rw [traceOneNorm_neg_one]
  push_cast
  ring

/-- The subtraction-free centered-square identity for the cubic GN kernel. -/
theorem four_mul_GN_three_eq_centered_square (u x : ℕ) :
    4 * DkMath.CosmicFormulaBinom.GN 3 u x =
      u ^ 2 + 3 * (2 * x + u) ^ 2 := by
  rw [GN_three_dual_explicit]
  ring

/-- A target equation is exactly the centered-square shell equation. -/
theorem GN_three_eq_target_iff_centered_square
    {p u x : ℕ} :
    DkMath.CosmicFormulaBinom.GN 3 u x = p ↔
      4 * p = u ^ 2 + 3 * (2 * x + u) ^ 2 := by
  constructor
  · intro h
    calc
      4 * p = 4 * DkMath.CosmicFormulaBinom.GN 3 u x := by rw [h]
      _ = u ^ 2 + 3 * (2 * x + u) ^ 2 :=
        four_mul_GN_three_eq_centered_square u x
  · intro h
    have hmul :
        4 * DkMath.CosmicFormulaBinom.GN 3 u x = 4 * p := by
      calc
        4 * DkMath.CosmicFormulaBinom.GN 3 u x =
            u ^ 2 + 3 * (2 * x + u) ^ 2 :=
          four_mul_GN_three_eq_centered_square u x
        _ = 4 * p := h.symm
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) hmul

/-- The unit-gap slice of the cubic shell. -/
theorem GN_three_one_eq_target_iff_centered_square
    {p x : ℕ} :
    DkMath.CosmicFormulaBinom.GN 3 1 x = p ↔
      4 * p = 1 + 3 * (2 * x + 1) ^ 2 := by
  simpa using (GN_three_eq_target_iff_centered_square (p := p) (u := 1) (x := x))

/-! ### Integral centered residual -/

/-- The integral zero-level-set residual of the degree-three centered shell. -/
def GNThreeCenteredResidual (p u x : ℤ) : ℤ :=
  3 * (2 * x + u) ^ 2 + u ^ 2 - 4 * p

/-- Natural target equality is equivalent to vanishing of the integral residual. -/
theorem GN_three_eq_target_iff_centeredResidual_eq_zero
    {p u x : ℕ} :
    DkMath.CosmicFormulaBinom.GN 3 u x = p ↔
      GNThreeCenteredResidual (p : ℤ) (u : ℤ) (x : ℤ) = 0 := by
  rw [GN_three_eq_target_iff_centered_square]
  constructor
  · intro h
    dsimp [GNThreeCenteredResidual]
    have hcast :
        (4 * p : ℤ) = (u ^ 2 + 3 * (2 * x + u) ^ 2 : ℕ) := by
      exact_mod_cast h
    push_cast at hcast
    omega
  · intro h
    dsimp [GNThreeCenteredResidual] at h
    have hcast :
        (4 * p : ℤ) = (u ^ 2 + 3 * (2 * x + u) ^ 2 : ℕ) := by
      push_cast
      omega
    exact_mod_cast hcast

/-! ### Lightweight regression anchors -/

example : DkMath.CosmicFormulaBinom.GN 3 2 1 = 13 := by
  rw [GN_three_dual_explicit]
  norm_num

example : ¬ ∃ x : ℕ, DkMath.CosmicFormulaBinom.GN 3 1 x = 13 := by
  rintro ⟨x, hx⟩
  rw [GN_three_dual_explicit] at hx
  have hxle : x ≤ 2 := by
    nlinarith [sq_nonneg (x : ℤ)]
  interval_cases x <;> norm_num at hx

end DkMath.NumberTheory
