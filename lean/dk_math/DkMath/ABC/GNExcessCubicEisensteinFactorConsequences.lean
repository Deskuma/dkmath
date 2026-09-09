/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNExcessCubicEisensteinCoordinates

#print "file: DkMath.ABC.GNExcessCubicEisensteinFactorConsequences"

/-!
# Conditional Eisenstein square-factor consequences

This module records only consequences of an explicitly supplied equality
`beta * gamma^2 = (a+2)+ω`.  It contains no factor search, existence theorem,
UFD argument, or counting statement.
-/

namespace DkMath.ABC

open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.NumberTheory.EisensteinCoordinates

local notation "tqNorm" => DkMath.NumberTheory.TraceOneQuadratic.norm

/-- The coefficient-one equation for an explicit shell factor equality. -/
theorem GNExcessCubicRealizedLargeModulusShellWitness_eisensteinFactor_coeff_one
    {X D a : ℕ} {b c m n : ℤ}
    (_ha : a ∈
      GNExcessCubicRealizedLargeModulusShellWitnessSpace X D)
    (hfac :
      eisensteinCoord b c * (eisensteinCoord m n) ^ 2 =
        eisensteinCoord ((a : ℤ) + 2) 1) :
    b * (2 * m * n - n ^ 2) + c * (m ^ 2 - 2 * m * n) = 1 := by
  exact eisenstein_mul_sq_eq_cubicCoord_snd hfac

/-- The square coefficients are coprime under an explicit shell factor
equality. -/
theorem GNExcessCubicRealizedLargeModulusShellWitness_eisensteinFactor_coefficients_isCoprime
    {X D a : ℕ} {b c m n : ℤ}
    (_ha : a ∈
      GNExcessCubicRealizedLargeModulusShellWitnessSpace X D)
    (hfac :
      eisensteinCoord b c * (eisensteinCoord m n) ^ 2 =
        eisensteinCoord ((a : ℤ) + 2) 1) :
    IsCoprime (2 * m * n - n ^ 2) (m ^ 2 - 2 * m * n) := by
  exact eisenstein_mul_sq_eq_cubicCoord_coefficients_isCoprime hfac

/-- The shell product is the norm product under an explicit factor equality. -/
theorem GNExcessCubicRealizedLargeModulusShellWitness_eisensteinFactor_norm
    {X D a : ℕ} {b c m n : ℤ}
    (ha : a ∈
      GNExcessCubicRealizedLargeModulusShellWitnessSpace X D)
    (hfac :
      eisensteinCoord b c * (eisensteinCoord m n) ^ 2 =
        eisensteinCoord ((a : ℤ) + 2) 1) :
    ((GNExcessCubicFullRepeatedModulus a *
        GNExcessCubicComplement a : ℕ) : ℤ) =
      tqNorm (eisensteinCoord b c) * tqNorm (eisensteinCoord m n) ^ 2 := by
  calc
    ((GNExcessCubicFullRepeatedModulus a *
        GNExcessCubicComplement a : ℕ) : ℤ) =
        tqNorm (eisensteinCoord ((a : ℤ) + 2) 1) :=
      GNExcessCubicRealizedLargeModulusShellWitness_product_eq_eisensteinNorm ha
    _ = tqNorm (eisensteinCoord b c) * tqNorm (eisensteinCoord m n) ^ 2 :=
      eisenstein_mul_sq_eq_cubicCoord_norm hfac

end DkMath.ABC

#print axioms DkMath.ABC.GNExcessCubicRealizedLargeModulusShellWitness_eisensteinFactor_coeff_one
#print axioms DkMath.ABC.GNExcessCubicRealizedLargeModulusShellWitness_eisensteinFactor_coefficients_isCoprime
#print axioms DkMath.ABC.GNExcessCubicRealizedLargeModulusShellWitness_eisensteinFactor_norm
