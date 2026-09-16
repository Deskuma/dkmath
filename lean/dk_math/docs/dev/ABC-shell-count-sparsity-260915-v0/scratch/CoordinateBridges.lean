import DkMath.ABC.GNExcessCubicMordellTransport
import DkMath.ABC.GNExcessCubicEisensteinSquareFactorProvider

namespace Scratch

/-- The instruction's `A,U,V` normalization of the existing production
Mordell transport. -/
theorem instruction_mordell_transform {A r y : ℤ}
    (h : y ^ 2 + 3 = A * r ^ 3) :
    (A * y) ^ 2 = (A * r) ^ 3 - 3 * A ^ 2 := by
  calc
    (A * y) ^ 2 = A ^ 2 * (y ^ 2 + 3) - 3 * A ^ 2 := by ring
    _ = A ^ 2 * (A * r ^ 3) - 3 * A ^ 2 := by rw [h]
    _ = (A * r) ^ 3 - 3 * A ^ 2 := by ring

/-- Direct bounds available from one canonical squarefull shell coordinate. -/
theorem squarefull_shell_parameter_bounds
    {D e r : ℕ} (he : 0 < e) (hr : 0 < r)
    (hhi : e ^ 2 * r ^ 3 < 2 * D) :
    r ^ 3 < 2 * D ∧ e ^ 2 < 2 * D := by
  have he2 : 1 ≤ e ^ 2 := Nat.one_le_pow 2 e he
  have hr3 : 1 ≤ r ^ 3 := Nat.one_le_pow 3 r hr
  constructor
  · exact lt_of_le_of_lt
      (calc r ^ 3 = 1 * r ^ 3 := by simp
        _ ≤ e ^ 2 * r ^ 3 := Nat.mul_le_mul_right _ he2)
      hhi
  · exact lt_of_le_of_lt
      (calc e ^ 2 = e ^ 2 * 1 := by simp
        _ ≤ e ^ 2 * r ^ 3 := Nat.mul_le_mul_left _ hr3)
      hhi

/-- Squarefree-square uniqueness shows that the coefficient
`A = 4*S*e^2` recovers positive `(S,e)`; then `U=A*r` and `V=A*y` recover
`r,y`. -/
theorem mordell_full_parameter_recovery
    {S e r y S' e' r' y' : ℕ}
    (hS : Squarefree S) (hS' : Squarefree S')
    (he : e ≠ 0) (he' : e' ≠ 0)
    (hA : 4 * S * e ^ 2 = 4 * S' * e' ^ 2)
    (hU : (4 * S * e ^ 2) * r = (4 * S' * e' ^ 2) * r')
    (hV : (4 * S * e ^ 2) * y = (4 * S' * e' ^ 2) * y') :
    S = S' ∧ e = e' ∧ r = r' ∧ y = y' := by
  have hA' : 4 * (S * e ^ 2) = 4 * (S' * e' ^ 2) := by
    simpa [mul_assoc] using hA
  have hbase : S * e ^ 2 = S' * e' ^ 2 :=
    Nat.mul_left_cancel (by decide : 0 < 4) hA'
  have hse := DkMath.ABC.nat_squarefree_square_decomposition_unique
    hS hS' he he' hbase
  have hSeq : S = S' := hse.1.symm
  have heeq : e = e' := hse.2.symm
  subst S'
  subst e'
  have hcoef : 0 < 4 * S * e ^ 2 := by
    have hSpos : 0 < S := Nat.pos_of_ne_zero hS.ne_zero
    positivity
  exact ⟨rfl, rfl, Nat.mul_left_cancel hcoef hU,
    Nat.mul_left_cancel hcoef hV⟩

end Scratch

#print axioms Scratch.instruction_mordell_transform
#print axioms Scratch.squarefull_shell_parameter_bounds
#print axioms Scratch.mordell_full_parameter_recovery
