/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNExcessCubicMordellIncidence
import DkMath.NumberTheory.EisensteinCoordinates

#print "file: DkMath.ABC.GNExcessCubicEisensteinCoordinates"

/-!
# Cubic bridge to neutral Eisenstein coordinates

This module only identifies the cubic quadratic and its shell-witness product
with the existing neutral `TraceOneInt (-1)` norm.  It does not assert an
Eisenstein factorization, uniqueness, or any counting statement.
-/

namespace DkMath.ABC

open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.NumberTheory.EisensteinCoordinates

local notation "tqNorm" => DkMath.NumberTheory.TraceOneQuadratic.norm

/-- The cubic quadratic is the neutral Eisenstein norm of `(a+2)+ω`. -/
theorem cubicQuadratic_eq_eisensteinNorm (a : ℕ) :
    ((a ^ 2 + 3 * a + 3 : ℕ) : ℤ) =
      tqNorm (eisensteinCoord ((a : ℤ) + 2) 1) := by
  rw [norm_eisensteinCoord]
  push_cast
  ring

/-- A shell witness carries the cubic quadratic as the neutral Eisenstein norm
of its modulus-complement product. -/
theorem GNExcessCubicRealizedLargeModulusShellWitness_product_eq_eisensteinNorm
    {X D a : ℕ}
    (ha : a ∈
      GNExcessCubicRealizedLargeModulusShellWitnessSpace X D) :
    ((GNExcessCubicFullRepeatedModulus a *
        GNExcessCubicComplement a : ℕ) : ℤ) =
      tqNorm (eisensteinCoord ((a : ℤ) + 2) 1) := by
  obtain ⟨_, _, _, _, _, hEq, _, _, _⟩ :=
    GNExcessCubicRealizedLargeModulusShellWitness_complement_packet ha
  calc
    ((GNExcessCubicFullRepeatedModulus a *
        GNExcessCubicComplement a : ℕ) : ℤ) =
        ((a ^ 2 + 3 * a + 3 : ℕ) : ℤ) := by
      exact_mod_cast hEq
    _ = tqNorm (eisensteinCoord ((a : ℤ) + 2) 1) :=
      cubicQuadratic_eq_eisensteinNorm a

end DkMath.ABC

#print axioms DkMath.ABC.cubicQuadratic_eq_eisensteinNorm
#print axioms DkMath.ABC.GNExcessCubicRealizedLargeModulusShellWitness_product_eq_eisensteinNorm
