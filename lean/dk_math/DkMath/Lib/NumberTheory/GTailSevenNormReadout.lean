/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EisensteinCoordinates
import DkMath.Lib.Cosmic.GTailSeven

#print "file: DkMath.Lib.NumberTheory.GTailSevenNormReadout"

/-!
# Typed quadratic norm readout of the selected seven-tail square

The plus-sign quadratic is a norm in the existing TraceOneInt (-1) ring.
These are norm-value equalities, not reverse element reconstruction or
prime-ideal/unit-class claims.
-/

namespace DkMath.Lib.NumberTheory

open DkMath.NumberTheory.TraceOneQuadratic DkMath.CosmicFormula

/-- Reverse the standard Eisenstein second coordinate to read the plus-sign quadratic. -/
def gtailSevenNormCoord (a b : ℕ) : TraceOneInt (-1) :=
  eisensteinCoord (a : ℤ) (-(b : ℤ))

/-- The chosen integral element has the literal positive coordinate pair. -/
theorem gtailSevenNormCoord_eq (a b : ℕ) :
    gtailSevenNormCoord a b = (⟨(a : ℤ), (b : ℤ)⟩ : TraceOneInt (-1)) := by
  simp [gtailSevenNormCoord, eisensteinCoord]

/-- The actual quadratic-ring norm equals the cast natural plus-sign quadratic. -/
theorem norm_gtailSevenNormCoord (a b : ℕ) :
    norm (gtailSevenNormCoord a b) = ((a ^ 2 + a * b + b ^ 2 : ℕ) : ℤ) := by
  rw [gtailSevenNormCoord, norm_eisensteinCoord]
  push_cast
  ring

/-- Read the square using existing norm multiplicativity, not a new polynomial norm. -/
theorem norm_gtailSevenNormCoord_sq (a b : ℕ) :
    norm ((gtailSevenNormCoord a b : TraceOneInt (-1)) ^ 2) =
      (((a ^ 2 + a * b + b ^ 2) ^ 2 : ℕ) : ℤ) := by
  simp only [pow_two, traceOne_norm_mul, norm_gtailSevenNormCoord, Nat.cast_mul]

/-- Divisibility of the scalar quadratic is equivalent to divisibility of its norm value. -/
theorem dvd_quadratic_iff_dvd_gtailSevenNormCoord (q a b : ℕ) :
    q ∣ a ^ 2 + a * b + b ^ 2 ↔ (q : ℤ) ∣ norm (gtailSevenNormCoord a b) := by
  rw [norm_gtailSevenNormCoord]
  exact Int.ofNat_dvd.symm

/-- The exact selected seventh interior is a scalar multiple of the norm of an element square. -/
theorem selectedBody_seven_interior_eq_norm_square (a b : ℕ) :
    selectedBody 7 (Finset.Ico 1 7) (a : ℤ) (b : ℤ) =
      7 * (a : ℤ) * (b : ℤ) * ((a + b : ℕ) : ℤ) *
        norm ((gtailSevenNormCoord a b : TraceOneInt (-1)) ^ 2) := by
  simp only [selectedBody_seven_interior, norm_gtailSevenNormCoord_sq,
    Nat.cast_add, Nat.cast_mul, Nat.cast_pow]

end DkMath.Lib.NumberTheory
