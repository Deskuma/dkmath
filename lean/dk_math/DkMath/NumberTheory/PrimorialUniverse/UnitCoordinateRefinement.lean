/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimorialUniverse.FiniteReservationEscape
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.PrimorialUniverse.UnitCoordinateRefinement"

/-!
# Unit-relative coordinates and integer refinement

This module starts the PUU unit-coordinate layer.  A positive real unit gives
natural coordinates for absolute real points through `X = n * u`.  An integer
refinement `coarse = k * fine` transports coordinate `n` to `n * k`.

The arithmetic label belongs to the chosen natural coordinate, not to the
absolute real point: a prime coarse coordinate can become a nonprime fine
coordinate under a nontrivial synchronized refinement, while the old prime
factor remains visible.  No rational/irrational common-lattice theorem,
PowerSwap bridge, primorial wheel, or Legendre consumer is introduced here.
-/

namespace DkMath.NumberTheory.PrimorialUniverse

/-! ## Positive units and coordinates -/

/-- A positive real scale used as a discrete unit. -/
structure PositiveUnit where
  val : ℝ
  pos : 0 < val

/-- An absolute real point has natural coordinate `n` in the unit `u`. -/
def HasUnitCoordinate (u : PositiveUnit) (n : ℕ) (X : ℝ) : Prop :=
  X = (n : ℝ) * u.val

@[simp] theorem hasUnitCoordinate_iff (u : PositiveUnit) (n : ℕ) (X : ℝ) :
    HasUnitCoordinate u n X ↔ X = (n : ℝ) * u.val :=
  Iff.rfl

/-- A point has a prime natural coordinate in the unit `u`. -/
def HasPrimeCoordinate (u : PositiveUnit) (X : ℝ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ HasUnitCoordinate u p X

/-- A fixed positive unit gives a unique natural coordinate to a point. -/
theorem unitCoordinate_unique
    {u : PositiveUnit} {m n : ℕ} {X : ℝ}
    (hm : HasUnitCoordinate u m X)
    (hn : HasUnitCoordinate u n X) :
    m = n := by
  have hmul : (m : ℝ) * u.val = (n : ℝ) * u.val := hm.symm.trans hn
  have hcast : (m : ℝ) = (n : ℝ) :=
    mul_right_cancel₀ (ne_of_gt u.pos) hmul
  exact_mod_cast hcast

/-! ## Integer synchronized refinement -/

/-- `UnitRefinesBy fine coarse k` means `coarse = k * fine`. -/
def UnitRefinesBy (fine coarse : PositiveUnit) (k : ℕ) : Prop :=
  coarse.val = (k : ℝ) * fine.val

/-- The point represented by a coarse coordinate is unchanged by refinement. -/
theorem unitRefinement_samePoint
    {fine coarse : PositiveUnit} {k n : ℕ}
    (href : UnitRefinesBy fine coarse k) :
    (n : ℝ) * coarse.val = ((n * k : ℕ) : ℝ) * fine.val := by
  calc
    (n : ℝ) * coarse.val = (n : ℝ) * ((k : ℝ) * fine.val) := by
      rw [href]
    _ = ((n : ℝ) * (k : ℝ)) * fine.val := by rw [mul_assoc]
    _ = ((n * k : ℕ) : ℝ) * fine.val := by rw [Nat.cast_mul]

/-- Transport a natural coordinate from a coarse unit to its fine unit. -/
theorem unitCoordinate_refine
    {fine coarse : PositiveUnit} {k n : ℕ} {X : ℝ}
    (href : UnitRefinesBy fine coarse k)
    (hX : HasUnitCoordinate coarse n X) :
    HasUnitCoordinate fine (n * k) X := by
  rw [hasUnitCoordinate_iff]
  exact hX.trans (unitRefinement_samePoint href)

/-! ## Prime-to-nonprime coordinate bridge -/

/-- A nontrivial integer refinement makes a prime coordinate nonprime.

The statement is deliberately about the fine natural coordinate.  It does
not assign a prime/composite label to the shared absolute real point `X`.
-/
theorem prime_coordinate_becomes_nonprime_under_nontrivial_refinement
    {fine coarse : PositiveUnit} {p k : ℕ} {X : ℝ}
    (href : UnitRefinesBy fine coarse k)
    (hX : HasUnitCoordinate coarse p X)
    (hp : Nat.Prime p)
    (hk : 1 < k) :
    HasUnitCoordinate fine (p * k) X ∧
      ¬ Nat.Prime (p * k) := by
  refine ⟨unitCoordinate_refine href hX, ?_⟩
  exact Nat.not_prime_mul hp.ne_one (Nat.ne_of_gt hk)

/-- The refinement packet also records persistence of the old prime factor. -/
theorem prime_coordinate_refinement_packet
    {fine coarse : PositiveUnit} {p k : ℕ} {X : ℝ}
    (href : UnitRefinesBy fine coarse k)
    (hX : HasUnitCoordinate coarse p X)
    (hp : Nat.Prime p)
    (hk : 1 < k) :
    HasUnitCoordinate fine (p * k) X ∧
      ¬ Nat.Prime (p * k) ∧
      p ∣ p * k := by
  refine ⟨unitCoordinate_refine href hX, ?_, dvd_mul_right p k⟩
  exact Nat.not_prime_mul hp.ne_one (Nat.ne_of_gt hk)

/-! ## Connection to finite prime-support escape -/

/-- Refinement cannot make a new prime factor belong to an old finite basis. -/
theorem refined_coordinate_not_supported_by_old_basis
    {S : Finset ℕ}
    {fine coarse : PositiveUnit}
    {q k : ℕ} {X : ℝ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hk : 1 < k)
    (href : UnitRefinesBy fine coarse k)
    (hX : HasUnitCoordinate coarse q X) :
    HasUnitCoordinate fine (q * k) X ∧
      ¬ PrimeSupportContainedIn S (q * k) := by
  refine ⟨unitCoordinate_refine href hX, ?_⟩
  exact newPrime_mul_not_primeSupportContainedIn hq hqS
    (Nat.zero_lt_one.trans hk)

/-! ## Concrete same-point regression -/

/-- The coarse unit `5` and fine unit `1` are positive real units. -/
def coarseUnitFive : PositiveUnit :=
  ⟨5, by norm_num⟩

def fineUnitOne : PositiveUnit :=
  ⟨1, by norm_num⟩

/-- `15 = 3 * 5 = 15 * 1`: prime and nonprime are coordinate-relative. -/
theorem three_at_five_eq_fifteen_at_one :
    HasUnitCoordinate coarseUnitFive 3 15 ∧
      HasUnitCoordinate fineUnitOne 15 15 ∧
      Nat.Prime 3 ∧
      ¬ Nat.Prime 15 := by
  norm_num [HasUnitCoordinate, coarseUnitFive, fineUnitOne]

end DkMath.NumberTheory.PrimorialUniverse
