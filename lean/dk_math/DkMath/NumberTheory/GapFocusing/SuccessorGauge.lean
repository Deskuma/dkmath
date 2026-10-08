/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.GapFocusing.UnitGauge
import DkMath.Lib.Algebra.PowerSubgroup

#print "file: DkMath.NumberTheory.GapFocusing.SuccessorGauge"

/-!
# Existing unit-power classes at coprime and adjacent exponents

The fixed-extraction relation from `UnitGauge` is exactly membership of the
unit ratio in the power image subgroup. For coprime exponents, simultaneous
class agreement is equivalent to product-exponent class agreement. This
connects the earlier arithmetic gauge relation to the neutral group CRT;
it does not identify it with prime divisors of GN values.
-/

namespace DkMath.NumberTheory.GapFocusing

open DkMath.Lib.Algebra

/-- The existing class relation is the power-subgroup condition on a unit ratio. -/
theorem sameUnitPowerClass_iff_mem_powerSubgroup
    {R : Type*} [CommMonoid R] (n : ℕ) (u v : Rˣ) :
    SameUnitPowerClass n u v ↔ u * v⁻¹ ∈ powerSubgroup Rˣ n := by
  rw [mem_powerSubgroup]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, by rw [ht]; simp [mul_assoc]⟩
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    calc
      u = (u * v⁻¹) * v := by simp
      _ = t ^ n * v := by rw [← ht]
      _ = v * t ^ n := mul_comm _ _

/-- The relation agrees with equality in the genuine quotient unit group. -/
theorem sameUnitPowerClass_iff_quotient_eq
    {R : Type*} [CommMonoid R] (n : ℕ) (u v : Rˣ) :
    SameUnitPowerClass n u v ↔
      (u : Rˣ ⧸ powerSubgroup Rˣ n) = (v : Rˣ ⧸ powerSubgroup Rˣ n) := by
  constructor
  · intro h
    apply Eq.symm
    apply QuotientGroup.eq.mpr
    simpa only [mul_comm] using (sameUnitPowerClass_iff_mem_powerSubgroup n u v).mp h
  · intro h
    apply (sameUnitPowerClass_iff_mem_powerSubgroup n u v).mpr
    simpa only [mul_comm] using QuotientGroup.eq.mp h.symm

/-- Coprime-exponent class tests determine exactly the product-exponent class. -/
theorem sameUnitPowerClass_mul_iff_of_coprime
    {R : Type*} [CommMonoid R] {n m : ℕ} (h : n.Coprime m) (u v : Rˣ) :
    SameUnitPowerClass (n * m) u v ↔
      SameUnitPowerClass n u v ∧ SameUnitPowerClass m u v := by
  rw [sameUnitPowerClass_iff_mem_powerSubgroup,
    ← powerSubgroup_inf_eq_mul_of_coprime h]
  change (u * v⁻¹ ∈ powerSubgroup Rˣ n ∧ u * v⁻¹ ∈ powerSubgroup Rˣ m) ↔ _
  rw [← sameUnitPowerClass_iff_mem_powerSubgroup, ← sameUnitPowerClass_iff_mem_powerSubgroup]

/-- Adjacent class tests give the product-exponent class, including degree zero. -/
theorem sameUnitPowerClass_successor_iff
    {R : Type*} [CommMonoid R] (d : ℕ) (u v : Rˣ) :
    SameUnitPowerClass (d * (d + 1)) u v ↔
      SameUnitPowerClass d u v ∧ SameUnitPowerClass (d + 1) u v :=
  sameUnitPowerClass_mul_iff_of_coprime
    (by simp [Nat.Coprime, Nat.add_comm d 1]) u v

end DkMath.NumberTheory.GapFocusing
