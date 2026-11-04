/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicConditionalSplit

#print "file: DkMathTest.FLT.FreyCyclotomicConditionalSplit"

namespace DkMathTest.FLT.FreyCyclotomicConditionalSplit

open DkMath.Lib.NumberTheory DkMath.Lib.Algebra
open CyclotomicPrimaryUnitSpace CyclotomicPrimaryCongruence KummerSelmerExact
open IsCyclotomicExtension
open scoped NumberField
set_option backward.isDefEq.respectTransparency false
noncomputable section

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private def two : (ZMod 7)ˣ := Units.mk0 2 (by decide)
private def six : (ZMod 7)ˣ := Units.mk0 6 (by decide)
private def three : (ZMod 7)ˣ := Units.mk0 3 (by decide)

-- The actual finite-field map has a nonzero class: a unit need not have a cube root.
example : classMapAlong 3 (RingHom.id (ZMod 7)) (two : UnitClass (ZMod 7) 3) ≠ 1 := by
  intro h
  obtain ⟨t, ht⟩ := (classMapAlong_mk_eq_one_iff 3 (RingHom.id (ZMod 7)) two).mp h
  have hno : ¬ ∃ x : ZMod 7, x ^ 3 = 2 := by decide
  exact hno ⟨(t : ZMod 7), ht⟩

-- The value 6 is not 1, while its cube class is 1, witnessed by the actual root 3.
example : (six : ZMod 7) ≠ 1 ∧
    classMapAlong 3 (RingHom.id (ZMod 7)) (six : UnitClass (ZMod 7) 3) = 1 := by
  refine ⟨by decide, ?_⟩
  exact (classMapAlong_mk_eq_one_iff 3 (RingHom.id (ZMod 7)) six).mpr ⟨three, by decide⟩

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev F := CyclotomicField 5 ℚ
private theorem hζ : IsPrimitiveRoot (zeta 5 ℚ F) 5 := zeta_spec 5 ℚ F

-- Actual residue cardinality and ramification, in the actual fifth cyclotomic number field.
example : Nat.card (NumberField.RingOfIntegers F ⧸ (ramifiedPlace hζ).asIdeal) = 5 :=
  ramified_residue_card hζ

example : (5 : NumberField.RingOfIntegers F) ∈ ramifiedIdeal hζ ^ 4 :=
  natCast_mem_ramifiedIdeal_pow hζ 4 (by decide)

-- The cubic quotient is meaningful: lambda^2 does not vanish modulo lambda^3.
example : (hζ.toInteger - 1) ^ 2 ∉ ramifiedIdeal hζ ^ 3 := by
  rw [ramifiedIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    pow_dvd_pow_iff hζ.zeta_sub_one_prime'.ne_zero hζ.zeta_sub_one_prime'.not_isUnit]
  omega

private def c : (NumberField.RingOfIntegers F)ˣ :=
  (hζ.toInteger_isPrimitiveRoot.geom_sum_isUnit (by decide : 2 ≤ 5)
    (by decide : Nat.Coprime 2 5)).unit

-- The chosen cyclotomic unit has the actual value 1+zeta.
example : (c : NumberField.RingOfIntegers F) = 1 + hζ.toInteger := by
  simpa only [c, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one]
    using (hζ.toInteger_isPrimitiveRoot.geom_sum_isUnit (by decide : 2 ≤ 5)
      (by decide : Nat.Coprime 2 5)).unit_spec

private theorem fifth_power_local :
    Additive.ofMul ((c ^ 5 : (NumberField.RingOfIntegers F)ˣ) :
      UnitClass (NumberField.RingOfIntegers F) 5) ∈ localPowerSpace F 5 := by
  have hclass : ((c ^ 5 : (NumberField.RingOfIntegers F)ˣ) :
      UnitClass (NumberField.RingOfIntegers F) 5) = 1 :=
    (QuotientGroup.eq_one_iff (c ^ 5)).mpr ⟨c, rfl⟩
  rw [hclass]
  exact (localPowerSpace F 5).zero_mem

-- A genuine fifth power of that same unit satisfies the proved cubic primary congruence.
example : ((c ^ 5 : (NumberField.RingOfIntegers F)ˣ) : NumberField.RingOfIntegers F) ^ 4 - 1 ∈
    ramifiedIdeal hζ ^ 3 :=
  pow_sub_one_mem_ramifiedIdeal_cube_of_local_power hζ (by decide) (c ^ 5) fifth_power_local

#print axioms KummerLocalPrimaryUnit.pow_sub_one_mem_cube_of_local_pow
#print axioms classMapAlong_mk_eq_one_iff
#print axioms mk_mem_localPowerSpace_iff
#print axioms mk_mem_primaryWeightSquareSpace_iff
#print axioms primaryWeightSquareSpace_eq_bot_iff_global_power
#print axioms natCast_mem_ramifiedIdeal_pow
#print axioms ramified_residue_card
#print axioms unit_pow_sub_one_mem_ramifiedIdeal
#print axioms pow_sub_one_mem_ramifiedIdeal_cube_of_local_power
#print axioms DkMath.FLT.Frey.Source.residual_kummer_primary_unit_witness
#print axioms DkMath.FLT.Frey.Source.residual_kummer_impossible_of_primary_unit_vanishing
#print axioms DkMath.FLT.Frey.Source.residual_cyclic_extension_nonsplit_impossible
#print axioms DkMath.FLT.Frey.Source.residual_cyclic_extension_has_stable_complement

end
end DkMathTest.FLT.FreyCyclotomicConditionalSplit
