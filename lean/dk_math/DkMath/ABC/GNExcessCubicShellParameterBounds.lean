/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNExcessCubicShellFiberUniqueness

#print "file: DkMath.ABC.GNExcessCubicShellParameterBounds"

/-!
# Deterministic height bounds for the cubic Pell parameter

This module is a finite range ledger.  It records the production inequality
`D^2 * T^3 < 54 * (X+1)^6` and the exact cardinality identity between shell
witnesses and represented canonical `(r,S)` pairs.  It contains no asymptotic
count, external theorem, or ABC statement.
-/

namespace DkMath.ABC

/-! ## Root-free height calculation -/

/-- Abstract height calculation from `D*S`, `r^3`, and `T = r*S`. -/
theorem pellParameter_height_cube_aux
    {X D S r T : ℕ}
    (hD : 0 < D)
    (hDS : D * S ≤ 3 * (X + 1) ^ 2)
    (hr : r ^ 3 < 2 * D)
    (hT : T = r * S) :
    D ^ 2 * T ^ 3 < 54 * (X + 1) ^ 6 := by
  have hDT : D * T ≤ r * (3 * (X + 1) ^ 2) := by
    calc
      D * T = r * (D * S) := by rw [hT]; ring
      _ ≤ r * (3 * (X + 1) ^ 2) := Nat.mul_le_mul_left r hDS
  have hcube : (D * T) ^ 3 ≤
      (r * (3 * (X + 1) ^ 2)) ^ 3 :=
    Nat.pow_le_pow_left hDT 3
  have hCpos : 0 < (3 * (X + 1) ^ 2) ^ 3 := by positivity
  have hstrict :
      (r * (3 * (X + 1) ^ 2)) ^ 3 <
        (2 * D) * (3 * (X + 1) ^ 2) ^ 3 := by
    rw [mul_pow]
    exact Nat.mul_lt_mul_of_pos_right hr hCpos
  have hcombined :
      (D * T) ^ 3 < (2 * D) * (3 * (X + 1) ^ 2) ^ 3 :=
    lt_of_le_of_lt hcube hstrict
  have hcancel :
      D * (D ^ 2 * T ^ 3) <
        D * (2 * (3 * (X + 1) ^ 2) ^ 3) := by
    calc
      D * (D ^ 2 * T ^ 3) = (D * T) ^ 3 := by ring
      _ < (2 * D) * (3 * (X + 1) ^ 2) ^ 3 := hcombined
      _ = D * (2 * (3 * (X + 1) ^ 2) ^ 3) := by ring
  have hrootfree :
      D ^ 2 * T ^ 3 < 2 * (3 * (X + 1) ^ 2) ^ 3 :=
    (Nat.mul_lt_mul_left hD).mp hcancel
  calc
    D ^ 2 * T ^ 3 < 2 * (3 * (X + 1) ^ 2) ^ 3 := hrootfree
    _ = 54 * (X + 1) ^ 6 := by ring

/-! ## The shell product wrapper -/

/-- A represented shell pair satisfies the product bound `D*S ≤ 3*(X+1)^2`.
-/
theorem GNExcessCubicRealizedLargeModulusShellIncidencePair_DS_le
    {X D M S : ℕ}
    (hMS : (M, S) ∈
      GNExcessCubicRealizedLargeModulusShellIncidencePairSpace X D) :
    D * S ≤ 3 * (X + 1) ^ 2 := by
  obtain ⟨a, ha, hpair, ha1, haX, hD, h2D, hlarge, hSpos, hSX,
      hSq, hCop, hEq⟩ :=
    GNExcessCubicRealizedLargeModulusShellIncidencePair_packet hMS
  calc
    D * S ≤ M * S := Nat.mul_le_mul_right S hD
    _ = a ^ 2 + 3 * a + 3 := hEq
    _ ≤ 3 * (X + 1) ^ 2 := by nlinarith

/-! ## Production Pell-parameter height -/

/-- Every represented Pell parameter lies in the root-free height range. -/
theorem GNExcessCubicRealizedLargeModulusShellPellParameter_height_cube
    {X D T : ℕ}
    (hT : T ∈
      GNExcessCubicRealizedLargeModulusShellPellParameterSpace X D) :
    D ^ 2 * T ^ 3 < 54 * (X + 1) ^ 6 := by
  obtain ⟨M, S, r, hMS, hrM, hTrS, _, hrCube, _, _⟩ :=
    GNExcessCubicRealizedLargeModulusShellPellParameter_packet hT
  exact pellParameter_height_cube_aux
    (by
      obtain ⟨a, ha, hpair, ha1, haX, hD, h2D, hlarge, hSpos, hSX,
          hSq, hCop, hEq⟩ :=
        GNExcessCubicRealizedLargeModulusShellIncidencePair_packet hMS
      omega)
    (GNExcessCubicRealizedLargeModulusShellIncidencePair_DS_le hMS)
    hrCube hTrS

/-! ## Witness-level height consumer -/

/-- The canonical parameter of every shell witness satisfies the height bound.
-/
theorem GNExcessCubicRealizedLargeModulusShellWitness_pellParameter_height_cube
    {X D a : ℕ}
    (ha : a ∈
      GNExcessCubicRealizedLargeModulusShellWitnessSpace X D) :
    D ^ 2 *
        (oddPart (GNExcessCubicFullRepeatedModulus a) *
          GNExcessCubicComplement a) ^ 3 <
      54 * (X + 1) ^ 6 := by
  let T := oddPart (GNExcessCubicFullRepeatedModulus a) *
    GNExcessCubicComplement a
  have hT : T ∈
      GNExcessCubicRealizedLargeModulusShellPellParameterSpace X D := by
    apply mem_GNExcessCubicRealizedLargeModulusShellPellParameterSpace_iff.mpr
    exact ⟨GNExcessCubicFullRepeatedModulus a,
      GNExcessCubicComplement a,
      Finset.mem_image.mpr ⟨a, ha, rfl⟩, rfl⟩
  simpa [T] using
    (GNExcessCubicRealizedLargeModulusShellPellParameter_height_cube hT)

/-! ## Exact represented canonical-pair image -/

/-- Canonical `(r,S)` pairs represented by witnesses in one shell. -/
noncomputable def GNExcessCubicRealizedLargeModulusShellCubeCoreComplementSpace
    (X D : ℕ) : Finset (ℕ × ℕ) :=
  (GNExcessCubicRealizedLargeModulusShellWitnessSpace X D).image
    (fun a =>
      (oddPart (GNExcessCubicFullRepeatedModulus a),
        GNExcessCubicComplement a))

theorem mem_GNExcessCubicRealizedLargeModulusShellCubeCoreComplementSpace_iff
    {X D r S : ℕ} :
    (r, S) ∈
        GNExcessCubicRealizedLargeModulusShellCubeCoreComplementSpace X D ↔
      ∃ a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D,
        oddPart (GNExcessCubicFullRepeatedModulus a) = r ∧
          GNExcessCubicComplement a = S := by
  simp [GNExcessCubicRealizedLargeModulusShellCubeCoreComplementSpace]

/-- The represented canonical-pair image has exactly the shell witness card.
-/
theorem GNExcessCubicRealizedLargeModulusShellCubeCoreComplementSpace_card
    (X D : ℕ) :
    (GNExcessCubicRealizedLargeModulusShellCubeCoreComplementSpace X D).card =
      GNExcessCubicRealizedLargeModulusShellWitnessCount X D := by
  unfold GNExcessCubicRealizedLargeModulusShellCubeCoreComplementSpace
    GNExcessCubicRealizedLargeModulusShellWitnessCount
  exact Finset.card_image_of_injOn
    (GNExcessCubicRealizedLargeModulusShellWitness_pair_injective X D)

end DkMath.ABC

#print axioms DkMath.ABC.pellParameter_height_cube_aux
#print axioms DkMath.ABC.GNExcessCubicRealizedLargeModulusShellPellParameter_height_cube
#print axioms DkMath.ABC.GNExcessCubicRealizedLargeModulusShellCubeCoreComplementSpace_card
