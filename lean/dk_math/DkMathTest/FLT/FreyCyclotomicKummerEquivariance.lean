/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicKummerEquivariance

namespace DkMathTest.FLT.FreyCyclotomicKummerEquivariance

open DkMath.Lib.NumberTheory CyclotomicKummerWeight CyclotomicKummerEquivariance
open KummerSelmer KummerSelmerClassMap KummerSelmerEquivariance
open IsDedekindDomain Polynomial
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

-- This really moves the quadratic generator; testing only the identity action would miss this.
example : conjugation (AdjoinRoot.root quadPoly) ≠ AdjoinRoot.root quadPoly := by
  intro h
  have hr : -AdjoinRoot.root quadPoly = AdjoinRoot.root quadPoly :=
    conjugation_root.symm.trans h
  have hz : AdjoinRoot.root quadPoly = 0 := by linear_combination -hr / 2
  have hs := root_sq
  rw [hz] at hs
  norm_num at hs

-- The actual fractional ideal (2+i) goes to (2-i) under the actual integer-ring restriction.
example : (integerAut conjugation).idealMap
    (FractionalIdeal.spanSingleton (NumberField.RingOfIntegers F)⁰ (2 + AdjoinRoot.root quadPoly)) =
      FractionalIdeal.spanSingleton (NumberField.RingOfIntegers F)⁰ (2 - AdjoinRoot.root quadPoly) := by
  rw [CompatibleAut.idealMap_span]
  congr 1
  change conjugation (2 + AdjoinRoot.root quadPoly) = _
  rw [map_add, map_ofNat]
  exact congrArg (fun x : F => 2 + x) conjugation_root

private def c : Fˣ := Units.mk0 (2 + AdjoinRoot.root quadPoly) (by
  intro h
  have hr : AdjoinRoot.root quadPoly = -2 := by linear_combination h
  have hs := root_sq
  rw [hr] at hs
  norm_num at hs)

private theorem cube_mem : Additive.ofMul ((c ^ 3 : Fˣ) : KummerClass F 3) ∈
    valuationSpace (R := NumberField.RingOfIntegers F) 3 := by
  have hq : ((c ^ 3 : Fˣ) : KummerClass F 3) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨c, rfl⟩
  rw [hq]
  exact (valuationSpace (R := NumberField.RingOfIntegers F) 3).zero_mem

-- Move an actual cube and its actual ideal root; the selected root is not an independent witness.
example :
    rootIdeal 3 (Units.map (integerAut conjugation).field.toMonoidHom (c ^ 3))
        ((integerAut conjugation).map_mem (c ^ 3) cube_mem) =
      toPrincipalIdeal (NumberField.RingOfIntegers F) F
        (Units.map (integerAut conjugation).field.toMonoidHom c) := by
  rw [CompatibleAut.rootIdeal_map _ (by decide : 0 < 3) (c ^ 3) cube_mem]
  have hr : rootIdeal 3 (c ^ 3) cube_mem =
      toPrincipalIdeal (NumberField.RingOfIntegers F) F c := by
    apply idealUnits_pow_injective (by decide : 0 < 3)
    dsimp only
    rw [rootIdeal_pow, map_pow]
  rw [hr, CompatibleAut.idealUnitsMap_principal]

-- Both group-action laws are checked on the real class group, including arbitrary classes.
example (z : ClassGroup (NumberField.RingOfIntegers F)) :
    classGroupAction (conjugation * conjugation) z =
      classGroupAction conjugation (classGroupAction conjugation z) := by
  exact congrArg (fun f : MulAut _ => f z) (map_mul classGroupAction conjugation conjugation)

example (z : ClassGroup (NumberField.RingOfIntegers F)) :
    classGroupAction (1 : F ≃ₐ[ℚ] F) z = z := by
  exact congrArg (fun f : MulAut _ => f z) (map_one classGroupAction)

#print axioms CompatibleAut.idealMap_span
#print axioms CompatibleAut.idealMap_refl
#print axioms CompatibleAut.idealMap_trans
#print axioms CompatibleAut.classGroupEquiv
#print axioms CompatibleAut.map_mem
#print axioms CompatibleAut.rootIdeal_map
#print axioms CompatibleAut.toClassGroup_equivariant
#print axioms CompatibleAut.toClassTorsion_equivariant
#print axioms CompatibleAut.classImage_weight
#print axioms classGroupAction
#print axioms classImage_weight_square
#print axioms DkMath.FLT.Frey.Source.residual_kummer_classImage_weight_square

end
end DkMathTest.FLT.FreyCyclotomicKummerEquivariance
