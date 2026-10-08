/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.PowerSubgroup
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

#print "file: DkMathTest.Lib.Algebra.PowerSubgroup"

/-!
# Power-subgroup regression and dependency audit

The zero-degree boundary is allowed. Integer units give a nontrivial square
quotient despite the adjacent CRT; a cyclic group of order four shows why the
coprime hypothesis on the intersection theorem cannot be omitted.
-/

namespace DkMathTest.Lib.Algebra.PowerSubgroup

open DkMath.Lib.Algebra

variable {G : Type*} [CommGroup G]

/-- Degree zero gives `G / {1} ≃ (G / {1}) × (G / G)`. -/
noncomputable def zeroBoundaryCRT :
    G ⧸ (⊥ : Subgroup G) ≃* (G ⧸ (⊥ : Subgroup G)) × (G ⧸ (⊤ : Subgroup G)) :=
  (QuotientGroup.quotientMulEquivOfEq (powerSubgroup_zero (G := G)).symm).trans
    ((powerQuotientSuccessorCRT 0).trans
      (MulEquiv.prodCongr (QuotientGroup.quotientMulEquivOfEq powerSubgroup_zero)
        (QuotientGroup.quotientMulEquivOfEq powerSubgroup_one)))

example (n : ℕ) (x : G) :
    powerQuotientSuccessorCRT n (x : G ⧸ powerSubgroup G (n * (n + 1))) =
      ((x : G ⧸ powerSubgroup G n), (x : G ⧸ powerSubgroup G (n + 1))) :=
  powerQuotientSuccessorCRT_apply_mk n x

/-- Integer units have only the identity as a square. -/
theorem integerUnitSquareSubgroup : powerSubgroup ℤˣ 2 = ⊥ := by
  ext x
  rw [mem_powerSubgroup, Subgroup.mem_bot]
  constructor
  · rintro ⟨u, rfl⟩
    rcases Int.units_eq_one_or u with rfl | rfl <;> simp
  · rintro rfl
    exact ⟨1, by simp⟩

/-- Adjacent exponents do not imply that each individual power map is surjective. -/
theorem integerNegativeUnitNotSquare : (-1 : ℤˣ) ∉ powerSubgroup ℤˣ 2 := by
  rw [integerUnitSquareSubgroup, Subgroup.mem_bot]
  intro h
  have hc := congrArg (fun u : ℤˣ => (u : ℤ)) h
  norm_num at hc

/-- A concrete quotient sector survives at degree two. -/
theorem integerSquareClassNontrivial :
    ((-1 : ℤˣ) : ℤˣ ⧸ powerSubgroup ℤˣ 2) ≠ 1 := by
  intro h
  exact integerNegativeUnitNotSquare ((QuotientGroup.eq_one_iff _).mp h)

/-- In the next quotient the same unit is a cube. -/
theorem integerCubeClassTrivial :
    ((-1 : ℤˣ) : ℤˣ ⧸ powerSubgroup ℤˣ 3) = 1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  exact ⟨-1, by simp [pow_succ]⟩

/-- Without coprimality the product-exponent intersection identity can fail. -/
theorem noncoprimeIntersectionNeProductPower :
    powerSubgroup (Multiplicative (ZMod 4)) 2 ⊓
      powerSubgroup (Multiplicative (ZMod 4)) 2 ≠
        powerSubgroup (Multiplicative (ZMod 4)) (2 * 2) := by
  intro h
  have htwo : Multiplicative.ofAdd (2 : ZMod 4) ∈
      powerSubgroup (Multiplicative (ZMod 4)) 2 := by
    refine ⟨Multiplicative.ofAdd (1 : ZMod 4), ?_⟩
    rfl
  have hfour : Multiplicative.ofAdd (2 : ZMod 4) ∈
      powerSubgroup (Multiplicative (ZMod 4)) (2 * 2) := by
    rw [← h]
    exact ⟨htwo, htwo⟩
  obtain ⟨a, ha⟩ := hfour
  have hc := congrArg Multiplicative.toAdd ha
  change (2 * 2) • Multiplicative.toAdd a = (2 : ZMod 4) at hc
  norm_num [nsmul_eq_mul] at hc
  rw [show (4 : ZMod 4) = 0 from rfl, zero_mul] at hc
  exact (by decide : (0 : ZMod 4) ≠ 2) hc

#print axioms DkMath.Lib.Algebra.powerSubgroup
#print axioms DkMath.Lib.Algebra.mem_powerSubgroup
#print axioms DkMath.Lib.Algebra.powerSubgroup_zero
#print axioms DkMath.Lib.Algebra.powerSubgroup_one
#print axioms DkMath.Lib.Algebra.coprime_pow_bezout
#print axioms DkMath.Lib.Algebra.exists_mul_pow_of_coprime
#print axioms DkMath.Lib.Algebra.powerSubgroup_sup_eq_top_of_coprime
#print axioms DkMath.Lib.Algebra.powerSubgroup_mul_le_inf
#print axioms DkMath.Lib.Algebra.powerSubgroup_inf_eq_mul_of_coprime
#print axioms DkMath.Lib.Algebra.powerQuotientPair
#print axioms DkMath.Lib.Algebra.powerQuotientPair_apply
#print axioms DkMath.Lib.Algebra.powerQuotientPair_ker
#print axioms DkMath.Lib.Algebra.powerQuotientPair_surjective
#print axioms DkMath.Lib.Algebra.powerQuotientCRT
#print axioms DkMath.Lib.Algebra.powerQuotientCRT_apply_mk
#print axioms DkMath.Lib.Algebra.powerSubgroup_sup_successor
#print axioms DkMath.Lib.Algebra.powerSubgroup_inf_successor
#print axioms DkMath.Lib.Algebra.exists_mul_pow_successor
#print axioms DkMath.Lib.Algebra.powerQuotientSuccessorCRT
#print axioms DkMath.Lib.Algebra.powerQuotientSuccessorCRT_apply_mk
#print axioms DkMath.Lib.Algebra.unitPowerSubgroup
#print axioms DkMath.Lib.Algebra.unitPowerSubgroup_sup_successor
#print axioms DkMath.Lib.Algebra.unitPowerSubgroup_inf_successor
#print axioms DkMath.Lib.Algebra.unitPowerQuotientSuccessorCRT
#print axioms DkMath.Lib.Algebra.unitPowerQuotientSuccessorCRT_apply_mk
#print axioms zeroBoundaryCRT
#print axioms integerUnitSquareSubgroup
#print axioms integerNegativeUnitNotSquare
#print axioms integerSquareClassNontrivial
#print axioms integerCubeClassTrivial
#print axioms noncoprimeIntersectionNeProductPower

end DkMathTest.Lib.Algebra.PowerSubgroup
