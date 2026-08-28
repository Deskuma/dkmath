/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.Frontier
import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorOrbit
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.Legendre.PrimorialWheelBridge"

/-!
# Legendre square-offset / primorial-wheel bridge

This module is the consumer-side dictionary between the bounded prime waves
of the Legendre layer and the finite prime-basis wheel of
`DkMath.NumberTheory.PrimorialUniverse`.  A covered square offset is exactly
an absolute reservation by `primeScalesUpTo n`; for `2 ≤ n`, non-cover is
therefore exactly a projected wheel survivor.  On a genuine square cell, the
existing Frontier theorem upgrades that survivor to primality.

The bridge is a reduction and does not prove that every square shell has an
escaping offset.  It does not move Legendre definitions into
`PrimorialUniverse`, and it introduces no square-hole propagation, gap bound,
PowerSwap, GN/CosmicFormula, PNT, or RH argument.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.PrimorialUniverse

/-! ## Bounded-prime adapters -/

/-- The bounded prime world is a finite prime basis. -/
theorem primeScalesUpTo_isFinitePrimeBasis (n : ℕ) :
    IsFinitePrimeBasis (primeScalesUpTo n) := by
  intro p hp
  exact (mem_primeScalesUpTo.mp hp).1

/-- For `2 ≤ n`, the bounded prime world contains its first prime `2`. -/
theorem primeScalesUpTo_nonempty_of_two_le
    {n : ℕ} (hn : 2 ≤ n) :
    (primeScalesUpTo n).Nonempty := by
  refine ⟨2, ?_⟩
  exact mem_primeScalesUpTo.mpr ⟨Nat.prime_two, hn⟩

/-! ## Cover and reservation dictionary -/

/-- Legendre cover is exactly reservation by the bounded prime basis. -/
theorem squareOffsetCovered_iff_reservedByPrimeBasis
    {n r : ℕ} :
    SquareOffsetCovered n r ↔
      ReservedByPrimeBasis (primeScalesUpTo n) (n ^ 2 + r) := by
  rfl

/-- Non-cover is exactly non-reservation by the bounded prime basis. -/
theorem not_squareOffsetCovered_iff_not_reservedByPrimeBasis
    {n r : ℕ} :
    ¬ SquareOffsetCovered n r ↔
      ¬ ReservedByPrimeBasis (primeScalesUpTo n) (n ^ 2 + r) := by
  exact not_congr squareOffsetCovered_iff_reservedByPrimeBasis

/-! ## Projected survivor dictionary -/

/-- For `2 ≤ n`, non-cover is exactly survivor status of the projected shell. -/
theorem not_squareOffsetCovered_iff_projection_survivor
    {n r : ℕ} (hn : 2 ≤ n) :
    ¬ SquareOffsetCovered n r ↔
      IsPrimeBasisWheelSurvivor (primeScalesUpTo n)
        (squareShellWheelProjection (primeScalesUpTo n) n r) := by
  calc
    ¬ SquareOffsetCovered n r ↔
        ¬ ReservedByPrimeBasis (primeScalesUpTo n) (n ^ 2 + r) :=
      not_squareOffsetCovered_iff_not_reservedByPrimeBasis
    _ ↔ IsPrimeBasisWheelSurvivor (primeScalesUpTo n)
        (squareShellWheelProjection (primeScalesUpTo n) n r) :=
      squareShell_not_reserved_iff_projection_survivor
        (primeScalesUpTo_isFinitePrimeBasis n)
        (primeScalesUpTo_nonempty_of_two_le hn) n r

/-! ## Square-shell primality -/

/-- In a square cell, primality is equivalent to avoiding all bounded waves. -/
theorem squareOffset_prime_iff_not_covered
    {n r : ℕ}
    (hn : 0 < n)
    (hr : SquareOffset n r) :
    Nat.Prime (n ^ 2 + r) ↔
      ¬ SquareOffsetCovered n r := by
  constructor
  · intro hp hcovered
    obtain ⟨q, hq, hqle, hqdiv⟩ :=
      squareOffsetCovered_iff_exists_prime_dvd.mp hcovered
    have hqp : q = n ^ 2 + r :=
      ((Nat.dvd_prime hp).mp hqdiv).resolve_left hq.ne_one
    have hpLower : n ^ 2 < n ^ 2 + r := by
      dsimp [SquareOffset] at hr
      omega
    have hnSq : n ≤ n ^ 2 := by nlinarith
    rw [hqp] at hqle
    omega
  · intro hnot
    apply prime_of_squareAnchoredSupportEscape hn hr
    exact supportDisjointFrom_primeScalesUpTo_square_add_iff_not_covered.mpr hnot

/-- In a square cell with `2 ≤ n`, primality is equivalent to projected survival. -/
theorem squareOffset_prime_iff_projection_survivor
    {n r : ℕ}
    (hn : 2 ≤ n)
    (hr : SquareOffset n r) :
    Nat.Prime (n ^ 2 + r) ↔
      IsPrimeBasisWheelSurvivor (primeScalesUpTo n)
        (squareShellWheelProjection (primeScalesUpTo n) n r) := by
  calc
    Nat.Prime (n ^ 2 + r) ↔ ¬ SquareOffsetCovered n r :=
      squareOffset_prime_iff_not_covered (by omega) hr
    _ ↔ IsPrimeBasisWheelSurvivor (primeScalesUpTo n)
        (squareShellWheelProjection (primeScalesUpTo n) n r) :=
      not_squareOffsetCovered_iff_projection_survivor hn

/-! ## Optional global reduction -/

/-- Legendre's conjecture is equivalent to projected wheel escape from `n = 2` on. -/
theorem legendreConjecture_iff_projectedWheelEscape_from_two :
    LegendreConjecture ↔
      ∀ n : ℕ, 2 ≤ n →
        ∃ r : ℕ,
          SquareOffset n r ∧
          IsPrimeBasisWheelSurvivor (primeScalesUpTo n)
            (squareShellWheelProjection (primeScalesUpTo n) n r) := by
  constructor
  · intro hLegendre n hn
    obtain ⟨p, hp, hcell⟩ := hLegendre n (by omega)
    obtain ⟨r, hr, hrEq⟩ :=
      (squareCell_iff_exists_squareOffset n p).mp hcell
    refine ⟨r, hr, ?_⟩
    have hp' : Nat.Prime (n ^ 2 + r) := by simpa [hrEq] using hp
    exact (squareOffset_prime_iff_projection_survivor hn hr).mp hp'
  · intro hEscape n hn
    by_cases hnOne : n = 1
    · subst n
      refine ⟨2, by norm_num [SquareCell]⟩
    · have hnTwo : 2 ≤ n := by omega
      obtain ⟨r, hr, hsurv⟩ := hEscape n hnTwo
      have hp : Nat.Prime (n ^ 2 + r) :=
        (squareOffset_prime_iff_projection_survivor hnTwo hr).mpr hsurv
      refine ⟨n ^ 2 + r, hp, ?_⟩
      exact (squareCell_iff_exists_squareOffset n (n ^ 2 + r)).mpr
        ⟨r, hr, rfl⟩

/-! ## Concrete regressions and the empty-basis boundary -/

/-- The `n = 4`, `6 → 30` bridge agrees on reservation, projection, and primality. -/
theorem primorialWheelBridge_four_one :
    primeScalesUpTo 4 = ({2, 3} : Finset ℕ) ∧
      squareShellWheelProjection ({2, 3} : Finset ℕ) 4 1 = 5 ∧
      Nat.Prime (4 ^ 2 + 1) ∧
      IsPrimeBasisWheelSurvivor (primeScalesUpTo 4)
        (squareShellWheelProjection (primeScalesUpTo 4) 4 1) := by
  have hSet : primeScalesUpTo 4 = ({2, 3} : Finset ℕ) := by decide
  refine ⟨hSet, squareShellWheelProjection_two_three_four_one, by norm_num, ?_⟩
  rw [hSet, squareShellWheelProjection_two_three_four_one]
  norm_num [IsPrimeBasisWheelSurvivor, ReservedByPrimeBasis,
    finitePrimeBasisProduct]

/-- At `n = 1`, the bounded prime basis and its current open-period wheel are empty. -/
theorem primeScalesUpTo_one_empty_wheel_boundary :
    primeScalesUpTo 1 = ∅ ∧
      finitePrimeBasisProduct (primeScalesUpTo 1) = 1 ∧
      primeBasisWheelSurvivors (primeScalesUpTo 1) = ∅ := by
  have hEmpty : primeScalesUpTo 1 = ∅ := by decide
  have hProduct : finitePrimeBasisProduct (primeScalesUpTo 1) = 1 := by
    rw [hEmpty]
    simp [finitePrimeBasisProduct]
  refine ⟨hEmpty, hProduct, ?_⟩
  ext r
  rw [mem_primeBasisWheelSurvivors_iff]
  simp only [IsPrimeBasisWheelSurvivor, hProduct]
  simp [ReservedByPrimeBasis, hEmpty]
  omega

end DkMath.NumberTheory.Legendre
