/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicKummerUnitEquivariance

namespace DkMathTest.FLT.FreyCyclotomicKummerUnitEquivariance

open DkMath.Lib.NumberTheory CyclotomicKummerWeight CyclotomicKummerEquivariance
open KummerSelmer KummerSelmerClassMap KummerSelmerEquivariance KummerSelmerExact
open KummerSelmerUnitEquivariance CyclotomicKummerUnitEquivariance
open DkMath.Lib.Algebra IsDedekindDomain Polynomial
open scoped nonZeroDivisors
set_option backward.isDefEq.respectTransparency false
noncomputable section

private def quadPoly : ℚ[X] := X ^ 2 - C (-1)

private instance : Fact (Irreducible quadPoly) := ⟨by
  apply (X_pow_sub_C_irreducible_iff_of_prime (by decide : Nat.Prime 2)).mpr
  intro z
  nlinarith [sq_nonneg z]⟩

private abbrev F := AdjoinRoot quadPoly

private theorem root_sq : (AdjoinRoot.root quadPoly) ^ 2 = (-1 : F) := by
  have h := AdjoinRoot.eval₂_root quadPoly
  change Polynomial.eval₂ (AdjoinRoot.of quadPoly) (AdjoinRoot.root quadPoly)
    (X ^ 2 - C (-1 : ℚ)) = 0 at h
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, map_neg, map_one] at h
  exact sub_eq_zero.mp h

private def conjugateHom : F →ₐ[ℚ] F :=
  AdjoinRoot.liftAlgHom quadPoly (Algebra.ofId ℚ F) (-AdjoinRoot.root quadPoly) (by
    change Polynomial.eval₂ (algebraMap ℚ F) (-AdjoinRoot.root quadPoly)
      (X ^ 2 - C (-1 : ℚ)) = 0
    rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    simp only [map_neg, map_one, neg_sq, root_sq, sub_self])

private theorem conjugate_root : conjugateHom (AdjoinRoot.root quadPoly) =
    -AdjoinRoot.root quadPoly := AdjoinRoot.liftAlgHom_root ..

private def conjugation : F ≃ₐ[ℚ] F :=
  AlgEquiv.ofAlgHom conjugateHom conjugateHom
    (AdjoinRoot.algHom_ext (by
      change conjugateHom (conjugateHom (AdjoinRoot.root quadPoly)) = _
      rw [conjugate_root, map_neg, conjugate_root, neg_neg]
      rfl))
    (AdjoinRoot.algHom_ext (by
      change conjugateHom (conjugateHom (AdjoinRoot.root quadPoly)) = _
      rw [conjugate_root, map_neg, conjugate_root, neg_neg]
      rfl))

private theorem conjugation_root : conjugation (AdjoinRoot.root quadPoly) =
    -AdjoinRoot.root quadPoly := by
  rw [conjugation, AlgEquiv.ofAlgHom_apply]
  exact conjugate_root

private def integralI : NumberField.RingOfIntegers F :=
  ⟨AdjoinRoot.root quadPoly, by
    refine ⟨X ^ 2 - C (-1 : ℤ), monic_X_pow_sub_C _ (by decide : 2 ≠ 0), ?_⟩
    rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    simp only [map_neg, map_one, root_sq, sub_self]⟩

private def iUnit : (NumberField.RingOfIntegers F)ˣ where
  val := integralI
  inv := -integralI
  val_inv := by
    apply Subtype.ext
    change AdjoinRoot.root quadPoly * -AdjoinRoot.root quadPoly = (1 : F)
    rw [mul_neg, ← pow_two, root_sq, neg_neg]
  inv_val := by
    apply Subtype.ext
    change -AdjoinRoot.root quadPoly * AdjoinRoot.root quadPoly = (1 : F)
    rw [neg_mul, ← pow_two, root_sq, neg_neg]

private theorem map_iUnit : Units.map (integerAut conjugation).integers.toMonoidHom iUnit = -iUnit := by
  apply Units.ext
  apply Subtype.ext
  exact conjugation_root

-- The actual conjugation moves an actual unit quotient class when p=0 (the quotient is by {1}).
-- This tests the all-exponent action API; the exactness/weight-transfer API still requires p>0.
example : unitClassAction 0 conjugation
    (iUnit : UnitClass (NumberField.RingOfIntegers F) 0) ≠
      (iUnit : UnitClass (NumberField.RingOfIntegers F) 0) := by
  intro h
  change unitClassMap 0 (integerAut conjugation) (iUnit : UnitClass (NumberField.RingOfIntegers F) 0) = _ at h
  rw [unitClassMap_mk, map_iUnit] at h
  have hd := QuotientGroup.eq_iff_div_mem.mp h
  rw [powerSubgroup_zero, Subgroup.mem_bot, div_eq_one] at hd
  have hr := congrArg (fun u : (NumberField.RingOfIntegers F)ˣ => (u.val : F)) hd
  change -AdjoinRoot.root quadPoly = AdjoinRoot.root quadPoly at hr
  have hz : AdjoinRoot.root quadPoly = 0 := by linear_combination -hr / 2
  have hs := root_sq
  rw [hz] at hs
  norm_num at hs

-- The same positive-exponent unit inclusion commutes with this nonidentity field automorphism.
example : (integerAut conjugation).selmerMap 2
    (unitInclusion 2 (by decide) (iUnit : UnitClass (NumberField.RingOfIntegers F) 2)) =
      unitInclusion 2 (by decide) ((-iUnit : (NumberField.RingOfIntegers F)ˣ) :
        UnitClass (NumberField.RingOfIntegers F) 2) := by
  rw [unitInclusion_equivariant, unitClassMap_mk, map_iUnit]

private def signSelmer : Selmer ℤ ℚ 2 :=
  IsDedekindDomain.selmerGroup.fromUnit (K := ℚ) (n := 2) (-1 : ℤˣ)

private theorem sign_ne_one : ((-1 : ℤˣ) : UnitClass ℤ 2) ≠ 1 := by
  intro h
  obtain ⟨v, hv⟩ := (QuotientGroup.eq_one_iff (-1 : ℤˣ)).mp h
  have hz := congrArg (fun u : ℤˣ => (u : ℤ)) hv
  change (v : ℤ) ^ 2 = -1 at hz
  nlinarith [sq_nonneg (v : ℤ)]

private theorem sign_class_zero : toClassTorsion 2 (by decide) signSelmer = 1 := by
  apply Subtype.ext
  exact (toClassGroup_eq_one_iff_unit 2 (by decide) signSelmer).mpr ⟨-1, rfl⟩

-- Zero class-group image has a unique nontrivial unit inverse image; it does not kill the sign.
example : unitPreimage 2 (by decide) signSelmer sign_class_zero = (-1 : ℤˣ) ∧
    unitPreimage 2 (by decide) signSelmer sign_class_zero ≠ 1 := by
  have he : unitPreimage 2 (by decide) signSelmer sign_class_zero =
      ((-1 : ℤˣ) : UnitClass ℤ 2) := unitPreimage_eq 2 (by decide) _ _ _ rfl
  exact ⟨he, he ▸ sign_ne_one⟩

-- Eigenvalue one is transferred to that same nonzero unit class by the actual injective inclusion.
example : unitClassLinearMap 2 (CompatibleAut.refl (R := ℤ) (F := ℚ))
    (Additive.ofMul ((-1 : ℤˣ) : UnitClass ℤ 2)) =
      (1 : ZMod 2) • Additive.ofMul ((-1 : ℤˣ) : UnitClass ℤ 2) := by
  apply unitClassLinearMap_weight 2 (by decide) _ signSelmer _ rfl
  have he : classMap 2 (CompatibleAut.refl (R := ℤ) (F := ℚ)).field.toRingHom signSelmer.val =
      signSelmer.val := congrArg Subtype.val (selmerMap_refl 2 signSelmer)
  simpa only [ZMod.val_one, pow_one] using he

-- p-torsion need not inject into the quotient modulo pth powers: the class of 3 in Z/9 is killed.
example : ∃ a : Multiplicative (ZMod 9), a ≠ 1 ∧ a ^ 3 = 1 ∧
    (a : Multiplicative (ZMod 9) ⧸ powerSubgroup (Multiplicative (ZMod 9)) 3) = 1 := by
  refine ⟨Multiplicative.ofAdd 3, by decide +kernel, by decide +kernel, ?_⟩
  exact (QuotientGroup.eq_one_iff _).mpr ⟨Multiplicative.ofAdd 1, by decide +kernel⟩

#print axioms unitClassEquiv
#print axioms selmerEquiv
#print axioms classTorsionEquiv
#print axioms unitInclusion_equivariant
#print axioms short_exact_equivariant
#print axioms existsUnique_unitClass
#print axioms unitPreimage_spec
#print axioms unitPreimage_equivariant
#print axioms unitClassLinearMap_weight
#print axioms unitClassAction
#print axioms selmerAction
#print axioms classTorsionAction
#print axioms numberField_short_exact_equivariant
#print axioms unitImage_ne_one
#print axioms unitImage_weight_square
#print axioms unit_of_classImage_eq_one_weight_square
#print axioms DkMath.FLT.Frey.Source.residual_kummer_unit_weight_square

end
end DkMathTest.FLT.FreyCyclotomicKummerUnitEquivariance
