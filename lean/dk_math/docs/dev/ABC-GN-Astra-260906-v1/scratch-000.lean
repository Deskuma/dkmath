import DkMath.ABC.GNExcessCubicPellParameterIncidence

/-!
# SOL-000 scratch: a root-free height bound for the Pell parameter

This file is deliberately outside `DkMath/`.  It records a successful research
lemma without changing the production API.  The theorem combines the product
incidence bound `D*S <= 3*(X+1)^2` with the square-cube bound `r^3 < 2*D`.
-/

namespace DkMath.ABC.SOL000Scratch

/-- An abstract, root-free form of the Pell-parameter height calculation. -/
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
  have hcube : (D * T) ^ 3 ≤ (r * (3 * (X + 1) ^ 2)) ^ 3 :=
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
      D * (D ^ 2 * T ^ 3) < D * (2 * (3 * (X + 1) ^ 2) ^ 3) := by
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

/-- Every production-realized shell Pell parameter obeys the root-free height
bound.  This is a scratch theorem, not a shell-cardinality estimate. -/
theorem realized_shell_pellParameter_height_cube
    {X D T : ℕ}
    (hT : T ∈ GNExcessCubicRealizedLargeModulusShellPellParameterSpace X D) :
    D ^ 2 * T ^ 3 < 54 * (X + 1) ^ 6 := by
  obtain ⟨M, S, r, hMS, hrM, hTrS, _, hrCube, _, _⟩ :=
    GNExcessCubicRealizedLargeModulusShellPellParameter_packet hT
  obtain ⟨a, _, _, _, haX, hDM, _, _, _, _, _, _, hEq⟩ :=
    GNExcessCubicRealizedLargeModulusShellIncidencePair_packet hMS
  have hF : a ^ 2 + 3 * a + 3 ≤ 3 * (X + 1) ^ 2 := by
    nlinarith
  have hDS : D * S ≤ 3 * (X + 1) ^ 2 := by
    calc
      D * S ≤ M * S := Nat.mul_le_mul_right S hDM
      _ = a ^ 2 + 3 * a + 3 := hEq
      _ ≤ 3 * (X + 1) ^ 2 := hF
  exact pellParameter_height_cube_aux (by omega) hDS hrCube hTrS

end DkMath.ABC.SOL000Scratch

#print axioms DkMath.ABC.SOL000Scratch.pellParameter_height_cube_aux
#print axioms DkMath.ABC.SOL000Scratch.realized_shell_pellParameter_height_cube
