/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimorialUniverse.WheelProjection
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.PrimorialUniverse.SquareAnchorOrbit"

/-!
# Square-anchor orbit on a finite wheel

This module records the provider-side finite orbit of `n^2` and `n^2 + r`
modulo a finite prime-basis product.  It connects absolute reservation to the
canonical one-period wheel survivor and proves coherence across a fresh-prime
wheel enlargement.

The module is independent of `DkMath.NumberTheory.Legendre`: it does not
define `SquareOffset`, `SquareOffsetCovered`, or a square-hole propagation
theorem, and it does not claim that an unreserved square-shell point is prime.
Wheel gaps, Euler-phi identification, PowerSwap, GN/CosmicFormula, PNT, and
RH are outside this checkpoint.
-/

namespace DkMath.NumberTheory.PrimorialUniverse

/-! ## Square-anchor coordinates -/

/-- The one-period coordinate of the square anchor `n^2`. -/
def squareAnchorWheelProjection (S : Finset ℕ) (n : ℕ) : ℕ :=
  primeBasisWheelProjection S (n ^ 2)

/-- The one-period coordinate of the square shell point `n^2 + r`. -/
def squareShellWheelProjection (S : Finset ℕ) (n r : ℕ) : ℕ :=
  primeBasisWheelProjection S (n ^ 2 + r)

/-- Adding a shell offset advances the anchor coordinate modulo the period. -/
theorem squareShellWheelProjection_eq_anchor_add
    {S : Finset ℕ} (_hS : IsFinitePrimeBasis S)
    (n r : ℕ) :
    squareShellWheelProjection S n r =
      (squareAnchorWheelProjection S n + r) %
        finitePrimeBasisProduct S := by
  simp [squareShellWheelProjection, squareAnchorWheelProjection,
    primeBasisWheelProjection, Nat.add_mod]

/-- Consecutive square anchors differ by the odd increment `2 * n + 1`. -/
theorem squareAnchorWheelProjection_succ
    {S : Finset ℕ} (_hS : IsFinitePrimeBasis S)
    (n : ℕ) :
    squareAnchorWheelProjection S (n + 1) =
      (squareAnchorWheelProjection S n + (2 * n + 1)) %
        finitePrimeBasisProduct S := by
  have hSquare : (n + 1) ^ 2 = n ^ 2 + (2 * n + 1) := by ring
  simp [squareAnchorWheelProjection, primeBasisWheelProjection, hSquare,
    Nat.add_mod]

/-- A whole old period does not change the square-anchor coordinate. -/
theorem squareAnchorWheelProjection_add_mul_period
    {S : Finset ℕ} (_hS : IsFinitePrimeBasis S)
    (n k : ℕ) :
    squareAnchorWheelProjection S
        (n + k * finitePrimeBasisProduct S) =
      squareAnchorWheelProjection S n := by
  unfold squareAnchorWheelProjection primeBasisWheelProjection
  rw [show (n + k * finitePrimeBasisProduct S) ^ 2 =
      n ^ 2 + (k * finitePrimeBasisProduct S) *
        (2 * n + k * finitePrimeBasisProduct S) by ring]
  rw [Nat.add_mod]
  have hMul : (k * finitePrimeBasisProduct S) *
      (2 * n + k * finitePrimeBasisProduct S) =
      finitePrimeBasisProduct S *
        (k * (2 * n + k * finitePrimeBasisProduct S)) := by ring
  rw [hMul]
  have hZero : (finitePrimeBasisProduct S *
      (k * (2 * n + k * finitePrimeBasisProduct S))) %
        finitePrimeBasisProduct S = 0 :=
    Nat.mod_eq_zero_of_dvd (dvd_mul_right _ _)
  rw [hZero]
  simp

/-- A fixed shell offset is periodic along the square-anchor orbit. -/
theorem squareShellWheelProjection_add_mul_period
    {S : Finset ℕ} (_hS : IsFinitePrimeBasis S)
    (n k r : ℕ) :
    squareShellWheelProjection S
        (n + k * finitePrimeBasisProduct S) r =
      squareShellWheelProjection S n r := by
  unfold squareShellWheelProjection
  rw [show (n + k * finitePrimeBasisProduct S) ^ 2 + r =
      (n ^ 2 + r) + (k * finitePrimeBasisProduct S) *
        (2 * n + k * finitePrimeBasisProduct S) by ring]
  unfold primeBasisWheelProjection
  rw [Nat.add_mod]
  have hMul : (k * finitePrimeBasisProduct S) *
      (2 * n + k * finitePrimeBasisProduct S) =
      finitePrimeBasisProduct S *
        (k * (2 * n + k * finitePrimeBasisProduct S)) := by ring
  rw [hMul]
  have hZero : (finitePrimeBasisProduct S *
      (k * (2 * n + k * finitePrimeBasisProduct S))) %
        finitePrimeBasisProduct S = 0 :=
    Nat.mod_eq_zero_of_dvd (dvd_mul_right _ _)
  rw [hZero]
  simp

/-! ## Reservation and survivor projection -/

/-- Reservation is unchanged when a point is replaced by its old-period residue. -/
theorem reservedByPrimeBasis_projection_iff
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    (x : ℕ) :
    ReservedByPrimeBasis S (primeBasisWheelProjection S x) ↔
      ReservedByPrimeBasis S x := by
  let M := finitePrimeBasisProduct S
  let r := primeBasisWheelProjection S x
  let k := x / M
  have hDecomp : x = r + k * M := by
    dsimp [r, k, M, primeBasisWheelProjection]
    exact (Nat.mod_add_div' x (finitePrimeBasisProduct S)).symm
  have hPeriod := reservedByPrimeBasis_add_mul_period_iff hS r k
  have hLeft : ReservedByPrimeBasis S x ↔
      ReservedByPrimeBasis S (r + k * M) := by
    rw [hDecomp]
  have hRight : ReservedByPrimeBasis S r ↔
      ReservedByPrimeBasis S x := hPeriod.symm.trans hLeft.symm
  simpa [r] using hRight

/-- The corresponding non-reservation equivalence for the canonical residue. -/
theorem not_reservedByPrimeBasis_projection_iff
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    (x : ℕ) :
    (¬ ReservedByPrimeBasis S (primeBasisWheelProjection S x)) ↔
      ¬ ReservedByPrimeBasis S x := by
  exact not_congr (reservedByPrimeBasis_projection_iff hS x)

/-- An unreserved natural projects to a one-period wheel survivor. -/
theorem not_reserved_iff_projection_wheelSurvivor
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (hSne : S.Nonempty)
    (x : ℕ) :
    (¬ ReservedByPrimeBasis S x) ↔
      IsPrimeBasisWheelSurvivor S
        (primeBasisWheelProjection S x) := by
  have hMpos : 0 < finitePrimeBasisProduct S :=
    Nat.pos_of_ne_zero (finitePrimeBasisProduct_ne_zero hS)
  have hMgt : 1 < finitePrimeBasisProduct S :=
    one_lt_finitePrimeBasisProduct_of_nonempty hS hSne
  constructor
  · intro hx
    have hProjNot : ¬ ReservedByPrimeBasis S
        (primeBasisWheelProjection S x) :=
      (not_reservedByPrimeBasis_projection_iff hS x).mpr hx
    have hlt : primeBasisWheelProjection S x <
        finitePrimeBasisProduct S := Nat.mod_lt _ hMpos
    have hpos : 0 < primeBasisWheelProjection S x := by
      by_contra hzero
      have hz : primeBasisWheelProjection S x = 0 :=
        Nat.eq_zero_of_not_pos hzero
      obtain ⟨p, hp⟩ := hSne
      exact hProjNot ⟨p, hp, by simp [hz]⟩
    exact ⟨hpos, hlt, hProjNot⟩
  · intro hr hReserved
    apply hr.2.2
    exact (reservedByPrimeBasis_projection_iff hS x).mpr hReserved

/-- Square-shell reservation is equivalent to the projected survivor predicate. -/
theorem squareShell_not_reserved_iff_projection_survivor
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (hSne : S.Nonempty)
    (n r : ℕ) :
    (¬ ReservedByPrimeBasis S (n ^ 2 + r)) ↔
      IsPrimeBasisWheelSurvivor S
        (squareShellWheelProjection S n r) := by
  simpa [squareShellWheelProjection] using
    (not_reserved_iff_projection_wheelSurvivor hS hSne (n ^ 2 + r))

/-! ## Nested-wheel coherence -/

/-- Reducing first modulo an enlarged period and then modulo the old period
agrees with reducing directly modulo the old period. -/
theorem primeBasisWheelProjection_insert_fresh_then_old
    {S : Finset ℕ}
    (_hS : IsFinitePrimeBasis S)
    {q : ℕ}
    (_hq : Nat.Prime q)
    (hqS : q ∉ S)
    (x : ℕ) :
    primeBasisWheelProjection S
        (primeBasisWheelProjection (insert q S) x) =
      primeBasisWheelProjection S x := by
  unfold primeBasisWheelProjection
  rw [finitePrimeBasisProduct_insert hqS]
  exact Nat.mod_mod_of_dvd x (by
    have h := dvd_mul_right (finitePrimeBasisProduct S) q
    rw [Nat.mul_comm] at h
    exact h)

/-- Square-shell projections are coherent across a fresh-prime wheel step. -/
theorem squareShellWheelProjection_insert_fresh_projects_old
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (n r : ℕ) :
    primeBasisWheelProjection S
        (squareShellWheelProjection (insert q S) n r) =
      squareShellWheelProjection S n r := by
  exact primeBasisWheelProjection_insert_fresh_then_old hS hq hqS
    (n ^ 2 + r)

/-! ## Visible `6 → 30` regression -/

/-- For `n = 4`, the `{2, 3}` square anchor is `16 % 6 = 4`. -/
theorem squareAnchorWheelProjection_two_three_four :
    squareAnchorWheelProjection ({2, 3} : Finset ℕ) 4 = 4 := by
  norm_num [squareAnchorWheelProjection, primeBasisWheelProjection,
    finitePrimeBasisProduct]

/-- The shell `4^2 + 1 = 17` projects to the old survivor `5` modulo `6`. -/
theorem squareShellWheelProjection_two_three_four_one :
    squareShellWheelProjection ({2, 3} : Finset ℕ) 4 1 = 5 := by
  norm_num [squareShellWheelProjection, primeBasisWheelProjection,
    finitePrimeBasisProduct]

/-- The same shell point is `17` modulo `30`, and then `5` modulo `6`. -/
theorem squareShellWheelProjection_two_three_five_four_one :
    squareShellWheelProjection ({2, 3, 5} : Finset ℕ) 4 1 = 17 ∧
      primeBasisWheelProjection ({2, 3} : Finset ℕ)
        (squareShellWheelProjection ({2, 3, 5} : Finset ℕ) 4 1) = 5 := by
  norm_num [squareShellWheelProjection, primeBasisWheelProjection,
    finitePrimeBasisProduct]

end DkMath.NumberTheory.PrimorialUniverse
