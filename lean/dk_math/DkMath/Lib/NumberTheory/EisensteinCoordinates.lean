/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.TraceOneQuadratic

#print "file: DkMath.Lib.NumberTheory.EisensteinCoordinates"

/-!
# Neutral Eisenstein coordinates in DkMath.Lib

The standard Eisenstein coordinate `m + n * ω` is represented in
`TraceOneInt (-1)` by `(m,-n)`, since `τ = -ω`.  All identities below use the
existing TraceOneQuadratic ring and norm; this module introduces no second
ring or norm API.
-/

namespace DkMath.Lib.NumberTheory

open DkMath.NumberTheory.TraceOneQuadratic

local notation "tqNorm" => DkMath.NumberTheory.TraceOneQuadratic.norm

/-- Standard Eisenstein coordinates inside `TraceOneInt (-1)`, with
`τ = -ω`. -/
def eisensteinCoord (m n : ℤ) : TraceOneInt (-1) := ⟨m, -n⟩

@[simp] theorem eisensteinCoord_fst (m n : ℤ) :
    (eisensteinCoord m n).fst = m := rfl

@[simp] theorem eisensteinCoord_snd (m n : ℤ) :
    (eisensteinCoord m n).snd = -n := rfl

/-- The neutral TraceOneQuadratic norm in standard Eisenstein coordinates. -/
theorem norm_eisensteinCoord (m n : ℤ) :
    tqNorm (eisensteinCoord m n) = m ^ 2 - m * n + n ^ 2 := by
  simp [eisensteinCoord, DkMath.NumberTheory.TraceOneQuadratic.norm]
  ring

/-- Multiplication in standard Eisenstein coordinates. -/
theorem eisensteinCoord_mul (a b c d : ℤ) :
    eisensteinCoord a b * eisensteinCoord c d =
      eisensteinCoord (a * c - b * d) (a * d + b * c - b * d) := by
  apply traceOne_ext <;> simp [eisensteinCoord] <;> ring

/-- The square of a standard Eisenstein coordinate pair. -/
theorem eisensteinCoord_sq (m n : ℤ) :
    (eisensteinCoord m n) ^ 2 =
      eisensteinCoord (m ^ 2 - n ^ 2) (2 * m * n - n ^ 2) := by
  rw [pow_two, eisensteinCoord_mul]
  congr 1 <;> ring

/-- Coordinates of `beta * gamma^2` in the neutral Eisenstein ring. -/
theorem eisensteinCoord_mul_sq (b c m n : ℤ) :
    eisensteinCoord b c * (eisensteinCoord m n) ^ 2 =
      eisensteinCoord
        (b * (m ^ 2 - n ^ 2) - c * (2 * m * n - n ^ 2))
        (b * (2 * m * n - n ^ 2) + c * (m ^ 2 - 2 * m * n)) := by
  rw [eisensteinCoord_sq, eisensteinCoord_mul]
  congr 1; ring

/-- Multiplicativity of the existing TraceOneQuadratic norm on `beta*gamma²`.
-/
theorem norm_eisensteinCoord_mul_sq (b c m n : ℤ) :
    tqNorm (eisensteinCoord b c * (eisensteinCoord m n) ^ 2) =
      tqNorm (eisensteinCoord b c) * tqNorm (eisensteinCoord m n) ^ 2 := by
  calc
    tqNorm (eisensteinCoord b c * (eisensteinCoord m n) ^ 2) =
        tqNorm (eisensteinCoord b c) *
          tqNorm ((eisensteinCoord m n) ^ 2) :=
      traceOne_norm_mul _ _
    _ = tqNorm (eisensteinCoord b c) * tqNorm (eisensteinCoord m n) ^ 2 := by
      rw [pow_two, traceOne_norm_mul]
      ring

/-- Explicit polynomial form of the `beta*gamma²` norm identity. -/
theorem norm_eisensteinCoord_mul_sq_polynomial (b c m n : ℤ) :
    let A := b * (m ^ 2 - n ^ 2) - c * (2 * m * n - n ^ 2)
    let B := b * (2 * m * n - n ^ 2) + c * (m ^ 2 - 2 * m * n)
    A ^ 2 - A * B + B ^ 2 =
      (b ^ 2 - b * c + c ^ 2) * (m ^ 2 - m * n + n ^ 2) ^ 2 := by
  dsimp
  rw [← norm_eisensteinCoord, ← norm_eisensteinCoord,
    ← norm_eisensteinCoord, ← eisensteinCoord_mul_sq,
    norm_eisensteinCoord_mul_sq]

/-- A coefficient-one relation is Bezout's identity for the two square
coefficients. -/
theorem eisenstein_square_coefficient_coprime {m n b c : ℤ}
    (h : b * (2 * m * n - n ^ 2) + c * (m ^ 2 - 2 * m * n) = 1) :
    IsCoprime (2 * m * n - n ^ 2) (m ^ 2 - 2 * m * n) := by
  exact ⟨b, c, h⟩

/-! ## Conditional cubic-coordinate consequences -/

/-- The first coordinate of an explicit `beta * gamma²` factor equality. -/
theorem eisenstein_mul_sq_eq_cubicCoord_fst
    {a b c m n : ℤ}
    (hfac :
      eisensteinCoord b c * (eisensteinCoord m n) ^ 2 =
        eisensteinCoord (a + 2) 1) :
    b * (m ^ 2 - n ^ 2) - c * (2 * m * n - n ^ 2) = a + 2 := by
  have hfst := congrArg TraceOneInt.fst hfac
  rw [eisensteinCoord_mul_sq] at hfst
  simpa [eisensteinCoord] using hfst

/-- The coefficient-one coordinate of an explicit `beta * gamma²` factor
equality. -/
theorem eisenstein_mul_sq_eq_cubicCoord_snd
    {a b c m n : ℤ}
    (hfac :
      eisensteinCoord b c * (eisensteinCoord m n) ^ 2 =
        eisensteinCoord (a + 2) 1) :
    b * (2 * m * n - n ^ 2) + c * (m ^ 2 - 2 * m * n) = 1 := by
  have hsnd := congrArg TraceOneInt.snd hfac
  rw [eisensteinCoord_mul_sq] at hsnd
  simp [eisensteinCoord] at hsnd
  linarith

/-- The coefficient-one equation from an explicit factor equality implies
coprimality of the two square coefficients. -/
theorem eisenstein_mul_sq_eq_cubicCoord_coefficients_isCoprime
    {a b c m n : ℤ}
    (hfac :
      eisensteinCoord b c * (eisensteinCoord m n) ^ 2 =
        eisensteinCoord (a + 2) 1) :
    IsCoprime (2 * m * n - n ^ 2) (m ^ 2 - 2 * m * n) := by
  exact eisenstein_square_coefficient_coprime
    (eisenstein_mul_sq_eq_cubicCoord_snd hfac)

/-- Norm multiplicativity under an explicit `beta * gamma²` factor equality. -/
theorem eisenstein_mul_sq_eq_cubicCoord_norm
    {a b c m n : ℤ}
    (hfac :
      eisensteinCoord b c * (eisensteinCoord m n) ^ 2 =
        eisensteinCoord (a + 2) 1) :
    tqNorm (eisensteinCoord (a + 2) 1) =
      tqNorm (eisensteinCoord b c) * tqNorm (eisensteinCoord m n) ^ 2 := by
  rw [← hfac]
  exact norm_eisensteinCoord_mul_sq b c m n

/-- Polynomial norm consequence of an explicit `beta * gamma²` factor equality. -/
theorem eisenstein_mul_sq_eq_cubicCoord_polynomial_norm
    {a b c m n : ℤ}
    (hfac :
      eisensteinCoord b c * (eisensteinCoord m n) ^ 2 =
        eisensteinCoord (a + 2) 1) :
    a ^ 2 + 3 * a + 3 =
      (b ^ 2 - b * c + c ^ 2) * (m ^ 2 - m * n + n ^ 2) ^ 2 := by
  calc
    a ^ 2 + 3 * a + 3 =
        ((a + 2) ^ 2 - (a + 2) * 1 + 1) := by ring
    _ = tqNorm (eisensteinCoord (a + 2) 1) :=
      (norm_eisensteinCoord (a + 2) 1).symm
    _ = tqNorm (eisensteinCoord b c) * tqNorm (eisensteinCoord m n) ^ 2 :=
      eisenstein_mul_sq_eq_cubicCoord_norm hfac
    _ = (b ^ 2 - b * c + c ^ 2) *
        (m ^ 2 - m * n + n ^ 2) ^ 2 := by
      rw [norm_eisensteinCoord, norm_eisensteinCoord]

end DkMath.Lib.NumberTheory

#print axioms DkMath.Lib.NumberTheory.norm_eisensteinCoord
#print axioms DkMath.Lib.NumberTheory.eisensteinCoord_mul
#print axioms DkMath.Lib.NumberTheory.eisensteinCoord_sq
#print axioms DkMath.Lib.NumberTheory.eisensteinCoord_mul_sq
#print axioms DkMath.Lib.NumberTheory.norm_eisensteinCoord_mul_sq
#print axioms DkMath.Lib.NumberTheory.eisenstein_square_coefficient_coprime
#print axioms DkMath.Lib.NumberTheory.eisenstein_mul_sq_eq_cubicCoord_fst
#print axioms DkMath.Lib.NumberTheory.eisenstein_mul_sq_eq_cubicCoord_snd
#print axioms DkMath.Lib.NumberTheory.eisenstein_mul_sq_eq_cubicCoord_coefficients_isCoprime
#print axioms DkMath.Lib.NumberTheory.eisenstein_mul_sq_eq_cubicCoord_norm
#print axioms DkMath.Lib.NumberTheory.eisenstein_mul_sq_eq_cubicCoord_polynomial_norm
