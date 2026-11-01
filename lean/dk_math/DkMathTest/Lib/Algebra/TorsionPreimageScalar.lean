/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.TorsionPreimageLocalComplement

#print "file: DkMathTest.Lib.Algebra.TorsionPreimageScalar"

namespace DkMathTest.Lib.Algebra.TorsionPreimageScalar

open DkMath.Lib.Algebra CyclicPrimePowerScalar TorsionPreimageQuotient

-- A genuine higher stage: multiplication by 4 fixes the 3-socle of Z/9,
-- and acts by 1 modulo 3K, while it does not fix all of K.
example (x : ZMod 9) :
    (4 • x - 1 • x) ∈ (nsmulAddMonoidHom 3 : ZMod 9 →+ ZMod 9).range := by
  exact sub_nsmul_mem_range_of_socle (by decide : Nat.Prime 3) (m := 2) (by decide)
    (by simp) (nsmulAddMonoidHom 4) 1 (by decide) x

example : (4 : ℕ) • (1 : ZMod 9) ≠ 1 • (1 : ZMod 9) := by decide

-- Cyclicity is essential. This noncyclic group has a nontrivial shear on K/3K
-- even though the same endomorphism fixes K[3] pointwise.
private abbrev Mixed := ZMod 9 × ZMod 3

private def shear : Mixed →+ Mixed where
  toFun x := (x.1, x.2 + ZMod.castHom (by decide : 3 ∣ 9) (ZMod 3) x.1)
  map_zero' := by ext <;> simp
  map_add' x y := by
    ext
    · rfl
    · simp only [Prod.fst_add, Prod.snd_add, map_add]
      abel

example : ∀ x : Mixed, 3 • x = 0 → shear x = 1 • x := by decide

example : shear (1, 0) - 1 • (1, 0) ∉ (nsmulAddMonoidHom 3 : Mixed →+ Mixed).range := by
  change ¬ ∃ y : Mixed, 3 • y = shear (1, 0) - 1 • (1, 0)
  decide

-- The subgroup K has order 2 inside (Z/4)^2. The horizontal subgroup F
-- maps to the actual complementary line in (2^-1 K)/K.
private abbrev Plane := ZMod 4 × ZMod 4

private def bottomLine : AddSubgroup Plane where
  carrier := {x | 2 • x.1 = 0 ∧ x.2 = 0}
  zero_mem' := by simp
  add_mem' ha hb := by simp_all [mul_add]
  neg_mem' ha := by simp_all

private def horizontal : AddSubgroup Plane :=
  (AddMonoidHom.snd (ZMod 4) (ZMod 4)).ker

private theorem bottom_le_horizontal : bottomLine ≤ horizontal := fun _ hx => hx.2

private theorem horizontal_le_preimage : horizontal ≤ preimage 2 bottomLine := by
  intro x hx
  change 2 • (2 • x.1) = 0 ∧ 2 • x.2 = 0
  have hx' : x.2 = 0 := hx
  constructor
  · have h : ∀ a : ZMod 4, 2 • (2 • a) = 0 := by decide
    exact h x.1
  · rw [hx', nsmul_zero]

private theorem horizontal_down : ∀ x ∈ horizontal, 2 • x = 0 → x ∈ bottomLine := by
  intro x hx hkill
  exact ⟨congrArg Prod.fst hkill, hx⟩

example : liftSubmodule 2 bottomLine (imageSubmodule 2 bottomLine horizontal) = horizontal :=
  lift_imageSubmodule 2 bottomLine horizontal bottom_le_horizontal horizontal_le_preimage

example : Disjoint (torsionImage 2 bottomLine) (imageSubmodule 2 bottomLine horizontal) :=
  disjoint_imageSubmodule 2 bottomLine horizontal bottom_le_horizontal horizontal_down

-- At a higher stage, pK need not vanish: the quotient target K/pK is required.
example : 2 • (2 : ZMod 8) ≠ 0 := by decide

private def evenEight : AddSubgroup (ZMod 8) := (nsmulAddMonoidHom 2).range

private def onePreimage : preimage 2 evenEight := ⟨1, ⟨1, rfl⟩⟩

-- The general map is nonzero for a concrete higher-stage class, even though
-- the old map V -> K would not be well-defined here (2K is nonzero).
example : quotientMultiplyMod 2 evenEight (quotientMap 2 evenEight onePreimage) ≠ 0 := by
  intro h
  have hC := (mem_torsionImage_iff_quotientMultiplyMod_eq_zero 2 evenEight _).mpr h
  obtain ⟨k, hk⟩ := (quotientMap_mem_torsionImage_iff 2 evenEight onePreimage).mp hC
  have hno : ¬ ∃ k : ZMod 8, (∃ a : ZMod 8, 2 • a = k) ∧ 2 • (1 : ZMod 8) = 2 • k := by
    decide
  exact hno ⟨k.val, k.property, hk⟩

#print axioms range_nsmul_eq_ker
#print axioms sub_nsmul_mem_range_of_socle
#print axioms socle_mem_of_prime_subgroup
#print axioms quotientMultiplyMod_surjective
#print axioms mem_torsionImage_iff_quotientMultiplyMod_eq_zero
#print axioms torsionImageQuotientEquiv
#print axioms representation_sub_nsmul_mem_torsionImage_of_cyclic
#print axioms lift_imageSubmodule
#print axioms isCompl_imageSubmodule

end DkMathTest.Lib.Algebra.TorsionPreimageScalar
