/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Tactic

#print "file: DkMath.Algebra.MetallicRatioCore.Basic"

namespace DkMath.Algebra.MetallicRatioCore

/--
A generic pair of scalar observations.

The source objects do not need to live in the scalar ring.  In particular,
complex eta terms can be converted into a real-valued pair with
`UnitPair.observe norm original mirrored`.
-/
structure UnitPair (R : Type*) where
  x : R
  u : R

namespace UnitPair

/-- Map both observed components through the same function. -/
def map {R S : Type*} (f : R → S) (p : UnitPair R) : UnitPair S :=
  ⟨f p.x, f p.u⟩

/-- Build a scalar pair by observing two arbitrary source objects. -/
def observe {α R : Type*} (f : α → R) (x u : α) : UnitPair R :=
  ⟨f x, f u⟩

@[simp] theorem map_x {R S : Type*} (f : R → S) (p : UnitPair R) :
    (p.map f).x = f p.x := rfl

@[simp] theorem map_u {R S : Type*} (f : R → S) (p : UnitPair R) :
    (p.map f).u = f p.u := rfl

@[simp] theorem observe_x {α R : Type*} (f : α → R) (x u : α) :
    (observe f x u).x = f x := rfl

@[simp] theorem observe_u {α R : Type*} (f : α → R) (x u : α) :
    (observe f x u).u = f u := rfl

end UnitPair

section CommRing

variable {R : Type*} [CommRing R]

/-- Positive-unit attached square core: `(x + u)^2`. -/
def unitAttachedCorePos (x u : R) : R :=
  (x + u) ^ 2

/-- Negative-unit attached square core: `(x - u)^2`. -/
def unitAttachedCoreNeg (x u : R) : R :=
  (x - u) ^ 2

/-- Metallic-ratio core in homogeneous unit scale. -/
def metallicCore (k : ℕ) (x u : R) : R :=
  x ^ 2 - (k : R) * u * x - u ^ 2

/-- Metallic beam before the vertical `u^2` height shift. -/
def metallicBeamCore (k : ℕ) (x u : R) : R :=
  x ^ 2 - (k : R) * u * x

/-- Negating the coordinate exchanges the two attached-unit square cores. -/
theorem unitAttachedCorePos_neg_x (x u : R) :
    unitAttachedCorePos (-x) u = unitAttachedCoreNeg x u := by
  unfold unitAttachedCorePos unitAttachedCoreNeg
  ring

/-- Negating the unit exchanges the two attached-unit square cores. -/
theorem unitAttachedCorePos_neg_u (x u : R) :
    unitAttachedCorePos x (-u) = unitAttachedCoreNeg x u := by
  unfold unitAttachedCorePos unitAttachedCoreNeg
  ring

/-- The sum removes the signed cross term and keeps the two square masses. -/
theorem unitAttachedCore_add (x u : R) :
    unitAttachedCorePos x u + unitAttachedCoreNeg x u =
      2 * (x ^ 2 + u ^ 2) := by
  unfold unitAttachedCorePos unitAttachedCoreNeg
  ring

/-- The difference removes the square masses and keeps the oriented product. -/
theorem unitAttachedCore_sub (x u : R) :
    unitAttachedCorePos x u - unitAttachedCoreNeg x u =
      4 * x * u := by
  unfold unitAttachedCorePos unitAttachedCoreNeg
  ring

/-- The metallic core is exactly the beam shifted downward by `u^2`. -/
theorem metallicCore_eq_heightShift (k : ℕ) (x u : R) :
    metallicCore k x u = metallicBeamCore k x u - u ^ 2 := by
  unfold metallicCore metallicBeamCore
  ring

/-- Zero height after shifting is the original beam observed at height `u^2`. -/
theorem metallicCore_eq_zero_iff_height (k : ℕ) (x u : R) :
    metallicCore k x u = 0 ↔ metallicBeamCore k x u = u ^ 2 := by
  rw [metallicCore_eq_heightShift, sub_eq_zero]

/-- The signed `k = 2` closure core is the square gap `(x - u)^2`. -/
theorem closedCore_two (x u : R) :
    x ^ 2 - 2 * u * x + u ^ 2 = unitAttachedCoreNeg x u := by
  unfold unitAttachedCoreNeg
  ring

namespace UnitPair

/-- Square of the sum of the two observed components. -/
def big (p : UnitPair R) : R :=
  unitAttachedCorePos p.x p.u

/-- Square of the difference of the two observed components. -/
def gap (p : UnitPair R) : R :=
  unitAttachedCoreNeg p.x p.u

/-- Oriented product preserved by a normalized mirror pair. -/
def product (p : UnitPair R) : R :=
  p.x * p.u

/-- Even square-mass component of the pair. -/
def squareMass (p : UnitPair R) : R :=
  p.x ^ 2 + p.u ^ 2

@[simp] theorem big_def (p : UnitPair R) :
    p.big = (p.x + p.u) ^ 2 := rfl

@[simp] theorem gap_def (p : UnitPair R) :
    p.gap = (p.x - p.u) ^ 2 := rfl

@[simp] theorem product_def (p : UnitPair R) :
    p.product = p.x * p.u := rfl

/-- Pair-level even-component decomposition. -/
theorem big_add_gap (p : UnitPair R) :
    p.big + p.gap = 2 * p.squareMass := by
  exact unitAttachedCore_add p.x p.u

/-- Pair-level odd-component decomposition. -/
theorem big_sub_gap (p : UnitPair R) :
    p.big - p.gap = 4 * p.product := by
  exact unitAttachedCore_sub p.x p.u

/-- Big is Gap plus four times the oriented product. -/
theorem big_eq_gap_add_four_mul_product (p : UnitPair R) :
    p.big = p.gap + 4 * p.product := by
  unfold big gap product unitAttachedCorePos unitAttachedCoreNeg
  ring

/-- Under unit-product normalization, `Big = Gap + 4`. -/
theorem big_eq_gap_add_four_of_product_eq_one
    (p : UnitPair R) (hproduct : p.product = 1) :
    p.big = p.gap + 4 := by
  rw [p.big_eq_gap_add_four_mul_product, hproduct]
  ring

/-- Under unit-product normalization, `Big = 4` exactly when `Gap = 0`. -/
theorem big_eq_four_iff_gap_eq_zero_of_product_eq_one
    (p : UnitPair R) (hproduct : p.product = 1) :
    p.big = 4 ↔ p.gap = 0 := by
  rw [p.big_eq_gap_add_four_of_product_eq_one hproduct]
  constructor <;> intro h
  · exact add_left_cancel (by simpa using h)
  · simpa [h]

end UnitPair

end CommRing

section Domain

variable {R : Type*} [CommRing R] [NoZeroDivisors R]

/-- The negative attached-unit core vanishes exactly when the two components agree. -/
theorem unitAttachedCoreNeg_eq_zero_iff (x u : R) :
    unitAttachedCoreNeg x u = 0 ↔ x = u := by
  constructor
  · intro h
    have hmul : (x - u) * (x - u) = 0 := by
      simpa [unitAttachedCoreNeg, pow_two] using h
    rcases mul_eq_zero.mp hmul with hsub | hsub
    · exact sub_eq_zero.mp hsub
    · exact sub_eq_zero.mp hsub
  · intro h
    subst u
    simp [unitAttachedCoreNeg]

namespace UnitPair

/-- Pair Gap vanishes exactly when its two observations agree. -/
theorem gap_eq_zero_iff (p : UnitPair R) :
    p.gap = 0 ↔ p.x = p.u := by
  exact unitAttachedCoreNeg_eq_zero_iff p.x p.u

end UnitPair

end Domain

section LinearOrderedRing

variable {R : Type*} [LinearOrderedRing R]

/-- Both attached-unit square cores are nonnegative. -/
theorem unitAttachedCorePos_nonneg (x u : R) :
    0 ≤ unitAttachedCorePos x u := by
  simp [unitAttachedCorePos]

/-- The closure Gap is nonnegative. -/
theorem unitAttachedCoreNeg_nonneg (x u : R) :
    0 ≤ unitAttachedCoreNeg x u := by
  simp [unitAttachedCoreNeg]

namespace UnitPair

/-- A nonnegative unit-product pair with zero Gap is forced to `(1, 1)`. -/
theorem eq_one_of_nonneg_of_product_eq_one_of_gap_eq_zero
    (p : UnitPair R)
    (hx : 0 ≤ p.x) (hu : 0 ≤ p.u)
    (hproduct : p.product = 1)
    (hgap : p.gap = 0) :
    p.x = 1 ∧ p.u = 1 := by
  have hxu : p.x = p.u := (p.gap_eq_zero_iff).mp hgap
  have hsq : p.x * p.x = 1 := by
    simpa [UnitPair.product, hxu] using hproduct
  have hxone : p.x = 1 := by
    nlinarith
  constructor
  · exact hxone
  · calc
      p.u = p.x := hxu.symm
      _ = 1 := hxone

end UnitPair

end LinearOrderedRing

end DkMath.Algebra.MetallicRatioCore
