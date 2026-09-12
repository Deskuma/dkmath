/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.PrincipalIdealPower

#print "file: DkMath.Lib.NumberTheory.UnitPowerSector"

/-!
# Unit power sectors

This module records the neutral interface for a unit group modulo p-th
powers.  A sector system supplies representatives and a completeness proof;
it does not assert that the p-th power map on units is surjective.
-/

namespace DkMath.Lib.NumberTheory

open scoped nonZeroDivisors

/-- Representatives for the quotient of units by p-th powers.

The base interface deliberately has no finiteness assumption.  A concrete
number ring may use a finite sector type, while a more general application
may provide any type of representatives.
-/
structure UnitPowerSectorSystem
    (R : Type*) [CommMonoidWithZero R] (p : ℕ) where
  Sector : Type
  rep : Sector → Rˣ
  complete : ∀ u : Rˣ, ∃ s : Sector, ∃ e : Rˣ, u = rep s * e ^ p

/-- Normalize a unit-weighted p-th power into an explicit unit sector. -/
theorem exists_sector_mul_pow_of_unit_mul_pow
    {R : Type*} [CommMonoidWithZero R] {p : ℕ}
    (S : UnitPowerSectorSystem R p)
    {a gamma : R} (u : Rˣ)
    (h : a = (u : R) * gamma ^ p) :
    ∃ s : S.Sector, ∃ delta : R,
      a = (S.rep s : R) * delta ^ p := by
  rcases S.complete u with ⟨s, e, he⟩
  have he' : (u : R) = (S.rep s : R) * (e : R) ^ p := by
    simpa using congrArg (fun v : Rˣ => (v : R)) he
  refine ⟨s, (e : R) * gamma, ?_⟩
  calc
    a = ((S.rep s : R) * (e : R) ^ p) * gamma ^ p := by rw [h, he']
    _ = (S.rep s : R) * ((e : R) * gamma) ^ p := by
      rw [mul_pow]
      ac_rfl

/-- Turn an associated p-th power into an explicit unit-sector endpoint. -/
theorem exists_sector_mul_pow_of_associated_pow
    {R : Type*} [CommMonoidWithZero R] {p : ℕ}
    (S : UnitPowerSectorSystem R p)
    {a gamma : R} (h : Associated a (gamma ^ p)) :
    ∃ s : S.Sector, ∃ delta : R,
      a = (S.rep s : R) * delta ^ p := by
  rcases h with ⟨u, hu⟩
  have ha : a = (↑(u⁻¹) : R) * gamma ^ p := by
    calc
      a = a * (u : R) * (↑(u⁻¹) : R) := by simp [mul_assoc]
      _ = gamma ^ p * (↑(u⁻¹) : R) := by rw [hu]
      _ = (↑(u⁻¹) : R) * gamma ^ p := by rw [mul_comm]
  exact exists_sector_mul_pow_of_unit_mul_pow S (u⁻¹) ha

/-- Replace the phase-16 unit endpoint by an explicit sector endpoint. -/
theorem exists_sector_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {I : Ideal R} {a : R} {p : ℕ}
    (S : UnitPowerSectorSystem R p)
    (hI0 : I ∈ (Ideal R)⁰)
    (hfree : classGroupPTorsionFreeAt R p)
    (hspan : Ideal.span ({a} : Set R) = I ^ p) :
    ∃ s : S.Sector, ∃ delta : R,
      a = (S.rep s : R) * delta ^ p := by
  rcases exists_unit_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
      hI0 hfree hspan with ⟨u, gamma, _hu, _hgamma, ha⟩
  let U : Rˣ := _hu.unit
  have hU : (U : R) = u := _hu.unit_spec
  apply exists_sector_mul_pow_of_unit_mul_pow S U
  calc
    a = u * gamma ^ p := ha
    _ = (U : R) * gamma ^ p := by rw [hU]

/-- The singleton sector system induced by surjectivity of the unit p-th power map. -/
def singletonUnitPowerSectorSystem
    {R : Type*} [CommMonoidWithZero R] {p : ℕ}
    (hunit : ∀ u : Rˣ, ∃ e : Rˣ, u = e ^ p) :
    UnitPowerSectorSystem R p where
  Sector := PUnit
  rep := fun _ => 1
  complete := by
    intro u
    rcases hunit u with ⟨e, he⟩
    refine ⟨PUnit.unit, e, ?_⟩
    simpa using he

/-- Recover the exact-power phase-16 endpoint from the singleton sector. -/
theorem exists_eq_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt_of_unit_pow_surjective
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {I : Ideal R} {a : R} {p : ℕ}
    (hI0 : I ∈ (Ideal R)⁰)
    (hfree : classGroupPTorsionFreeAt R p)
    (hunit : ∀ u : Rˣ, ∃ e : Rˣ, u = e ^ p)
    (hspan : Ideal.span ({a} : Set R) = I ^ p) :
    ∃ delta : R, a = delta ^ p := by
  rcases exists_sector_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
      (singletonUnitPowerSectorSystem hunit) hI0 hfree hspan with
    ⟨_s, delta, hdelta⟩
  exact ⟨delta, by simpa [singletonUnitPowerSectorSystem] using hdelta⟩

end DkMath.Lib.NumberTheory
