/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNExcessCubicShellParameterBounds

#print "file: DkMath.ABC.GNExcessCubicMordellTransport"

/-!
# Exact Mordell-coordinate transport for the cubic Pell witness

This module records only the polynomial coordinate bridge from a production
square-cube/Pell witness to an integral Mordell equation.  It contains no
elliptic-curve structure, integral-point count, rank estimate, asymptotic
bound, or ABC statement.
-/

namespace DkMath.ABC

/-! ## Generic polynomial identities -/

/-- Integer transport from `y²+3=4*S*r³*u²` to Mordell form. -/
theorem cubicPell_to_Mordell_identity {y S r u : ℤ}
    (h : y ^ 2 + 3 = 4 * S * r ^ 3 * u ^ 2) :
    (4 * S * u ^ 2 * y) ^ 2 =
      (4 * S * u ^ 2 * r) ^ 3 - 48 * S ^ 2 * u ^ 4 := by
  calc
    (4 * S * u ^ 2 * y) ^ 2 =
        16 * S ^ 2 * u ^ 4 * (y ^ 2 + 3) - 48 * S ^ 2 * u ^ 4 := by ring
    _ = 16 * S ^ 2 * u ^ 4 * (4 * S * r ^ 3 * u ^ 2) -
        48 * S ^ 2 * u ^ 4 := by rw [h]
    _ = (4 * S * u ^ 2 * r) ^ 3 - 48 * S ^ 2 * u ^ 4 := by ring

/-- Natural-number, subtraction-free form of the Mordell transport. -/
theorem cubicPell_to_Mordell_identity_nat {y S r u : ℕ}
    (h : y ^ 2 + 3 = 4 * S * r ^ 3 * u ^ 2) :
    (4 * S * u ^ 2 * y) ^ 2 + 48 * S ^ 2 * u ^ 4 =
      (4 * S * u ^ 2 * r) ^ 3 := by
  calc
    (4 * S * u ^ 2 * y) ^ 2 + 48 * S ^ 2 * u ^ 4 =
        16 * S ^ 2 * u ^ 4 * (y ^ 2 + 3) := by ring
    _ = 16 * S ^ 2 * u ^ 4 * (4 * S * r ^ 3 * u ^ 2) := by rw [h]
    _ = (4 * S * u ^ 2 * r) ^ 3 := by ring

/-! ## Production square-cube conic -/

/-- A shell witness has the canonical cubic Pell equation
`y²+3 = 4*S*r³*u²`, with `r=oddPart M` and the squareful quotient `u`. -/
theorem GNExcessCubicRealizedLargeModulusShellWitness_squareCube_conic
    {X D a : ℕ}
    (ha : a ∈
      GNExcessCubicRealizedLargeModulusShellWitnessSpace X D) :
    (2 * a + 3) ^ 2 + 3 =
      4 * GNExcessCubicComplement a *
        (oddPart (GNExcessCubicFullRepeatedModulus a)) ^ 3 *
        (GNExcessCubicSquarefulQuotient
          (GNExcessCubicFullRepeatedModulus a)) ^ 2 := by
  let M := GNExcessCubicFullRepeatedModulus a
  let S := GNExcessCubicComplement a
  let r := oddPart M
  let u := GNExcessCubicSquarefulQuotient M
  have hMS : (M, S) ∈
      GNExcessCubicRealizedLargeModulusShellIncidencePairSpace X D :=
    Finset.mem_image.mpr ⟨a, ha, rfl⟩
  obtain ⟨_, _, _, _, _, hEq, _, _, _⟩ :=
    GNExcessCubicRealizedLargeModulusShellWitness_complement_packet ha
  have hMspace : M ∈ GNExcessCubicRealizedLargeModulusSpace X := by
    have hW := mem_GNExcessCubicRealizedLargeModulusShellWitnessSpace_iff.mp ha
    rw [← GNExcessCubicRealizedLargeWitnessSpace_image_eq_modulusSpace X]
    exact Finset.mem_image.mpr ⟨a, hW.1, rfl⟩
  have hpos := GNExcessCubicRealizedLargeModulusSpace_pos hMspace
  have hfull := GNExcessCubicRealizedLargeModulusSpace_squarefull hMspace
  have hcanon := squareful_eq_squareQuotient_sq_mul_oddPart_cube
    (Nat.ne_of_gt hpos) hfull
  have hdisc := cubicQuadratic_discriminant_identity a
  calc
    (2 * a + 3) ^ 2 + 3 = 4 * (a ^ 2 + 3 * a + 3) := hdisc.symm
    _ = 4 * (M * S) := by rw [hEq]
    _ = 4 * S * r ^ 3 * u ^ 2 := by
      rw [hcanon]
      dsimp [M, S, r, u]
      ring

/-! ## Production Mordell identity -/

/-- A production shell witness maps to the exact subtraction-free Mordell
equation in the canonical coordinates. -/
theorem GNExcessCubicRealizedLargeModulusShellWitness_mordell_identity
    {X D a : ℕ}
    (ha : a ∈
      GNExcessCubicRealizedLargeModulusShellWitnessSpace X D) :
    (4 * GNExcessCubicComplement a *
        (GNExcessCubicSquarefulQuotient
          (GNExcessCubicFullRepeatedModulus a)) ^ 2 *
        (2 * a + 3)) ^ 2 +
        48 * (GNExcessCubicComplement a) ^ 2 *
          (GNExcessCubicSquarefulQuotient
            (GNExcessCubicFullRepeatedModulus a)) ^ 4 =
      (4 * GNExcessCubicComplement a *
        (GNExcessCubicSquarefulQuotient
          (GNExcessCubicFullRepeatedModulus a)) ^ 2 *
        oddPart (GNExcessCubicFullRepeatedModulus a)) ^ 3 := by
  have hconic := GNExcessCubicRealizedLargeModulusShellWitness_squareCube_conic ha
  exact cubicPell_to_Mordell_identity_nat hconic

/-! ## Fixed-coefficient coordinate injectivity -/

/-- For positive fixed `(S,u)`, the Mordell coordinates are injective in
`(a,r)`.  This is only cancellation; it does not say that arbitrary integral
Mordell points arise from production witnesses. -/
theorem mordellCoordinates_injective_fixed_SU
    {S u a₁ a₂ r₁ r₂ : ℕ}
    (hS : 0 < S) (hu : 0 < u)
    (hZ : 4 * S * u ^ 2 * r₁ = 4 * S * u ^ 2 * r₂)
    (hY : 4 * S * u ^ 2 * (2 * a₁ + 3) =
      4 * S * u ^ 2 * (2 * a₂ + 3)) :
    r₁ = r₂ ∧ a₁ = a₂ := by
  have hcoef : 0 < 4 * S * u ^ 2 := by positivity
  have hr : r₁ = r₂ := Nat.mul_left_cancel hcoef hZ
  have hy : 2 * a₁ + 3 = 2 * a₂ + 3 := Nat.mul_left_cancel hcoef hY
  exact ⟨hr, by omega⟩

end DkMath.ABC

#print axioms DkMath.ABC.cubicPell_to_Mordell_identity
#print axioms DkMath.ABC.cubicPell_to_Mordell_identity_nat
#print axioms DkMath.ABC.GNExcessCubicRealizedLargeModulusShellWitness_squareCube_conic
#print axioms DkMath.ABC.GNExcessCubicRealizedLargeModulusShellWitness_mordell_identity
#print axioms DkMath.ABC.mordellCoordinates_injective_fixed_SU
