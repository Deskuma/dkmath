/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorOrbit
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhase"

/-!
# Square-anchor phase symmetry

This provider-side module records the phase relation induced by the square
anchor modulo a finite prime-basis period.  Equal phases give equal projected
shell coordinates for every fixed offset, and therefore equal reservation
patterns.  The results are finite wheel invariants only: they do not assert
escape existence, a gap bound, a Legendre provider, or any analytic theorem.
-/

namespace DkMath.NumberTheory.PrimorialUniverse

/-! ## Same phase -/

/-- Two anchors have the same square phase in the finite wheel. -/
def SameSquareAnchorPhase (S : Finset ℕ) (a b : ℕ) : Prop :=
  squareAnchorWheelProjection S a = squareAnchorWheelProjection S b

/-- Same-square phase is reflexive. -/
theorem sameSquareAnchorPhase_refl (S : Finset ℕ) (n : ℕ) :
    SameSquareAnchorPhase S n n :=
  rfl

/-- Same-square phase is symmetric. -/
theorem sameSquareAnchorPhase_symm {S : Finset ℕ} {a b : ℕ}
    (hab : SameSquareAnchorPhase S a b) :
    SameSquareAnchorPhase S b a :=
  hab.symm

/-- Same-square phase is transitive. -/
theorem sameSquareAnchorPhase_trans {S : Finset ℕ} {a b c : ℕ}
    (hab : SameSquareAnchorPhase S a b)
    (hbc : SameSquareAnchorPhase S b c) :
    SameSquareAnchorPhase S a c :=
  hab.trans hbc

/-! ## Period and reflection -/

/-- Translating an anchor by a whole wheel period preserves its square phase. -/
theorem sameSquareAnchorPhase_add_mul_period
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    (n k : ℕ) :
    SameSquareAnchorPhase S n
      (n + k * finitePrimeBasisProduct S) := by
  exact (squareAnchorWheelProjection_add_mul_period hS n k).symm

/-- Reflection `n ↦ M - n` preserves square phase inside one period. -/
theorem squareAnchorPhase_reflect
    {S : Finset ℕ}
    (_hS : IsFinitePrimeBasis S)
    {n : ℕ}
    (hn : n ≤ finitePrimeBasisProduct S) :
    SameSquareAnchorPhase S n
      (finitePrimeBasisProduct S - n) := by
  change n ^ 2 % finitePrimeBasisProduct S =
    (finitePrimeBasisProduct S - n) ^ 2 % finitePrimeBasisProduct S
  by_cases hsmall : 2 * n ≤ finitePrimeBasisProduct S
  · have hEq :
        (finitePrimeBasisProduct S - n) ^ 2 =
          n ^ 2 + finitePrimeBasisProduct S *
            (finitePrimeBasisProduct S - 2 * n) := by
      nlinarith [Nat.sub_add_cancel hn,
        Nat.sub_add_cancel hsmall]
    rw [hEq]
    simp [Nat.add_mod]
  · have hlarge : finitePrimeBasisProduct S ≤ 2 * n := by omega
    have hEq :
        n ^ 2 =
          (finitePrimeBasisProduct S - n) ^ 2 +
            finitePrimeBasisProduct S * (2 * n - finitePrimeBasisProduct S) := by
      nlinarith [Nat.sub_add_cancel hn,
        Nat.sub_add_cancel hlarge]
    rw [hEq]
    simp [Nat.add_mod]

/-! ## Fixed-offset projection invariant -/

/-- Same square phase gives the same projected shell coordinate at every offset. -/
theorem squareShellProjection_eq_of_sameAnchorPhase
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {a b : ℕ}
    (hab : SameSquareAnchorPhase S a b)
    (r : ℕ) :
    squareShellWheelProjection S a r =
      squareShellWheelProjection S b r := by
  rw [squareShellWheelProjection_eq_anchor_add hS,
    squareShellWheelProjection_eq_anchor_add hS, hab]

/-! ## Reservation-pattern invariant -/

/-- Same phase gives identical absolute finite-basis reservation status. -/
theorem reservedByPrimeBasis_square_add_iff_of_sameAnchorPhase
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {a b : ℕ}
    (hab : SameSquareAnchorPhase S a b)
    (r : ℕ) :
    ReservedByPrimeBasis S (a ^ 2 + r) ↔
      ReservedByPrimeBasis S (b ^ 2 + r) := by
  calc
    ReservedByPrimeBasis S (a ^ 2 + r) ↔
        ReservedByPrimeBasis S (squareShellWheelProjection S a r) := by
      simpa [squareShellWheelProjection] using
        (reservedByPrimeBasis_projection_iff hS (a ^ 2 + r)).symm
    _ ↔ ReservedByPrimeBasis S (squareShellWheelProjection S b r) := by
      rw [squareShellProjection_eq_of_sameAnchorPhase hS hab r]
    _ ↔ ReservedByPrimeBasis S (b ^ 2 + r) := by
      simpa [squareShellWheelProjection] using
        reservedByPrimeBasis_projection_iff hS (b ^ 2 + r)

/-- Same phase also gives identical non-reservation status. -/
theorem not_reservedByPrimeBasis_square_add_iff_of_sameAnchorPhase
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {a b : ℕ}
    (hab : SameSquareAnchorPhase S a b)
    (r : ℕ) :
    (¬ ReservedByPrimeBasis S (a ^ 2 + r)) ↔
      ¬ ReservedByPrimeBasis S (b ^ 2 + r) := by
  exact not_congr (reservedByPrimeBasis_square_add_iff_of_sameAnchorPhase
    hS hab r)

/-- Reflection preserves the reservation pattern of every shell offset. -/
theorem reservedByPrimeBasis_square_reflect_iff
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {n : ℕ}
    (hn : n ≤ finitePrimeBasisProduct S)
    (r : ℕ) :
    ReservedByPrimeBasis S (n ^ 2 + r) ↔
      ReservedByPrimeBasis S
        ((finitePrimeBasisProduct S - n) ^ 2 + r) := by
  exact reservedByPrimeBasis_square_add_iff_of_sameAnchorPhase hS
    (squareAnchorPhase_reflect hS hn) r

/-! ## Visible `M = 6` regression -/

private theorem isFinitePrimeBasis_two_three :
    IsFinitePrimeBasis ({2, 3} : Finset ℕ) := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl <;> norm_num

/-- The `{2, 3}` wheel has period `6` and reflects phases `1 ↔ 5`, `2 ↔ 4`. -/
theorem squareAnchorPhase_two_three_reflection_regression :
    finitePrimeBasisProduct ({2, 3} : Finset ℕ) = 6 ∧
      SameSquareAnchorPhase ({2, 3} : Finset ℕ) 1 5 ∧
      SameSquareAnchorPhase ({2, 3} : Finset ℕ) 2 4 := by
  have hS := isFinitePrimeBasis_two_three
  have hM := finitePrimeBasisProduct_two_three
  have hn1 : (1 : ℕ) ≤ finitePrimeBasisProduct ({2, 3} : Finset ℕ) := by
    omega
  have hn2 : (2 : ℕ) ≤ finitePrimeBasisProduct ({2, 3} : Finset ℕ) := by
    omega
  refine ⟨hM, ?_, ?_⟩
  · simpa [finitePrimeBasisProduct] using
      (squareAnchorPhase_reflect hS (n := 1) hn1)
  · simpa [finitePrimeBasisProduct] using
      (squareAnchorPhase_reflect hS (n := 2) hn2)

/-- Reflected `{2, 3}` anchors reserve the same visible shell offsets. -/
theorem reservedByPrimeBasis_two_three_reflection_regression :
    (ReservedByPrimeBasis ({2, 3} : Finset ℕ) (1 ^ 2 + 1) ↔
      ReservedByPrimeBasis ({2, 3} : Finset ℕ) (5 ^ 2 + 1)) ∧
    (ReservedByPrimeBasis ({2, 3} : Finset ℕ) (1 ^ 2 + 2) ↔
      ReservedByPrimeBasis ({2, 3} : Finset ℕ) (5 ^ 2 + 2)) := by
  have hS := isFinitePrimeBasis_two_three
  have hM := finitePrimeBasisProduct_two_three
  have hn1 : (1 : ℕ) ≤ finitePrimeBasisProduct ({2, 3} : Finset ℕ) := by
    omega
  refine ⟨?_, ?_⟩
  · have h := reservedByPrimeBasis_square_reflect_iff hS (n := 1) hn1 1
    rw [hM] at h
    exact h
  · have h := reservedByPrimeBasis_square_reflect_iff hS (n := 1) hn1 2
    rw [hM] at h
    exact h

end DkMath.NumberTheory.PrimorialUniverse
