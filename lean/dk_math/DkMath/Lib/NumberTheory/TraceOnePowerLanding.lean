/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.TraceOneLatticeLanding

#print "file: DkMath.Lib.NumberTheory.TraceOnePowerLanding"

/-!
# General TraceOne power/Core-image landing

This module records the square image inside the existing `TraceOneInt s`
carrier.  It is a receiver/criterion layer: no square-root or power provider
is introduced.
-/

namespace DkMath.Lib.NumberTheory

open DkMath.NumberTheory.TraceOneQuadratic

local notation "traceNorm" => DkMath.NumberTheory.TraceOneQuadratic.norm

/-- Coordinates of a square in the arbitrary TraceOne quadratic carrier. -/
theorem traceOne_sq_coordinates (s m n : ℤ) :
    (⟨m, n⟩ : TraceOneInt s) ^ 2 =
      ⟨m ^ 2 + s * n ^ 2, 2 * m * n + n ^ 2⟩ := by
  rw [pow_two]
  apply traceOne_ext <;> simp
  · ring
  · ring

/-- Norm multiplicativity for arbitrary natural powers. -/
theorem traceOne_norm_pow (x : TraceOneInt s) (r : ℕ) :
    traceNorm (x ^ r) = traceNorm x ^ r := by
  induction r with
  | zero =>
      simp [DkMath.NumberTheory.TraceOneQuadratic.norm]
  | succ r ih =>
      rw [pow_succ, traceOne_norm_mul, ih, pow_succ]

/-- Norm consequence of an already supplied power factorization. -/
theorem traceOne_norm_eq_norm_mul_pow_of_eq
    {s : ℤ} {alpha beta gamma : TraceOneInt s} {r : ℕ}
    (h : alpha = beta * gamma ^ r) :
    traceNorm alpha = traceNorm beta * traceNorm gamma ^ r := by
  rw [h, traceOne_norm_mul, traceOne_norm_pow]

/-- Exact square/Core-image landing criterion in conjugate coordinates. -/
theorem traceOne_sq_core_landing_iff
    {s : ℤ} {alpha beta : TraceOneInt s}
    (hNorm : traceNorm beta ≠ 0) :
    (∃ gamma : TraceOneInt s, alpha = beta * gamma ^ 2) ↔
      ∃ m n : ℤ,
        (alpha * conj beta).fst =
            traceNorm beta * (m ^ 2 + s * n ^ 2) ∧
          (alpha * conj beta).snd =
            traceNorm beta * (2 * m * n + n ^ 2) := by
  constructor
  · rintro ⟨gamma, hgamma⟩
    rcases gamma with ⟨m, n⟩
    have hprod : alpha * conj beta =
        DkMath.NumberTheory.TraceOneQuadratic.ofInt s (traceNorm beta) *
          (⟨m, n⟩ : TraceOneInt s) ^ 2 := by
      calc
        alpha * conj beta =
            (beta * (⟨m, n⟩ : TraceOneInt s) ^ 2) * conj beta := by
              rw [hgamma]
        _ = (beta * conj beta) *
            (⟨m, n⟩ : TraceOneInt s) ^ 2 := by ring
        _ = DkMath.NumberTheory.TraceOneQuadratic.ofInt s
            (traceNorm beta) * (⟨m, n⟩ : TraceOneInt s) ^ 2 := by
              rw [traceOne_mul_conj]
    rw [traceOne_sq_coordinates] at hprod
    refine ⟨m, n, ?_, ?_⟩
    · simpa [DkMath.NumberTheory.TraceOneQuadratic.ofInt] using
        congrArg TraceOneInt.fst hprod
    · simpa [DkMath.NumberTheory.TraceOneQuadratic.ofInt] using
        congrArg TraceOneInt.snd hprod
  · rintro ⟨m, n, hfst, hsnd⟩
    let gamma : TraceOneInt s := ⟨m, n⟩
    have hscalar :
        DkMath.NumberTheory.TraceOneQuadratic.ofInt s (traceNorm beta) *
            gamma ^ 2 = alpha * conj beta := by
      rw [traceOne_sq_coordinates]
      apply traceOne_ext
      · simpa [gamma, DkMath.NumberTheory.TraceOneQuadratic.ofInt] using
          hfst.symm
      · simpa [gamma, DkMath.NumberTheory.TraceOneQuadratic.ofInt] using
          hsnd.symm
    have hprod : alpha * conj beta = (beta * gamma ^ 2) * conj beta := by
      calc
        alpha * conj beta =
            DkMath.NumberTheory.TraceOneQuadratic.ofInt s
              (traceNorm beta) * gamma ^ 2 := hscalar.symm
        _ = (beta * conj beta) * gamma ^ 2 := by rw [traceOne_mul_conj]
        _ = (beta * gamma ^ 2) * conj beta := by ring
    have hNormConj : traceNorm (conj beta) ≠ 0 := by
      simpa only [traceOne_norm_conj] using hNorm
    refine ⟨gamma, ?_⟩
    exact traceOne_mul_right_cancel_of_norm_ne_zero hNormConj hprod

/-- A square/Core-image factorization implies the corresponding norm identity. -/
theorem traceOne_norm_eq_norm_mul_sq_of_eq
    {s : ℤ} {alpha beta gamma : TraceOneInt s}
    (h : alpha = beta * gamma ^ 2) :
    traceNorm alpha = traceNorm beta * traceNorm gamma ^ 2 := by
  exact traceOne_norm_eq_norm_mul_pow_of_eq h

/-- Lattice landing is strictly weaker than square/Core-image landing. -/
theorem traceOne_lattice_landing_not_square :
    (1 : TraceOneInt 0) ∣ (⟨2, 0⟩ : TraceOneInt 0) ∧
      ¬ ∃ gamma : TraceOneInt 0,
        (⟨2, 0⟩ : TraceOneInt 0) = 1 * gamma ^ 2 := by
  constructor
  · exact one_dvd _
  · rintro ⟨gamma, hgamma⟩
    rcases gamma with ⟨m, n⟩
    have hfst := congrArg TraceOneInt.fst hgamma
    simp [pow_two] at hfst
    have hmle : m ≤ 1 := by
      nlinarith [sq_nonneg (m - 1)]
    have hmge : -1 ≤ m := by
      nlinarith [sq_nonneg (m + 1)]
    have hm : m = -1 ∨ m = 0 ∨ m = 1 := by omega
    rcases hm with rfl | rfl | rfl <;> norm_num at hfst

end DkMath.Lib.NumberTheory

#print axioms DkMath.Lib.NumberTheory.traceOne_sq_coordinates
#print axioms DkMath.Lib.NumberTheory.traceOne_norm_pow
#print axioms DkMath.Lib.NumberTheory.traceOne_norm_eq_norm_mul_pow_of_eq
#print axioms DkMath.Lib.NumberTheory.traceOne_sq_core_landing_iff
#print axioms DkMath.Lib.NumberTheory.traceOne_norm_eq_norm_mul_sq_of_eq
#print axioms DkMath.Lib.NumberTheory.traceOne_lattice_landing_not_square
