/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyGoodReductionTowerObstruction
import Mathlib.FieldTheory.Finite.GaloisField

namespace DkMathTest.FLT.FreyGoodReductionTowerObstruction

open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open FiniteFixedQuotient FiniteFieldFrobeniusFixed EllipticFrobeniusFixedReduction

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- A genuine extension residue field: fixed fifth powers in F_25 descend to F_5.
example (x : GaloisField 5 2) (hx : x ^ 5 = x) :
    ∃ a : ZMod 5, algebraMap (ZMod 5) (GaloisField 5 2) a = x := by
  exact exists_preimage_of_pow_card_eq (ZMod 5) (GaloisField 5 2) x
    (by simpa only [ZMod.card] using hx)

-- The entire extension field is not fixed. The residue field must not be treated as F_5.
example : ∃ x : GaloisField 5 2, x ^ 5 ≠ x := by
  by_contra h
  push Not at h
  have hs : Function.Surjective (algebraMap (ZMod 5) (GaloisField 5 2)) := fun x =>
    exists_preimage_of_pow_card_eq (ZMod 5) (GaloisField 5 2) x (by simpa only [ZMod.card] using h x)
  have hc := Nat.card_le_card_of_surjective _ hs
  rw [GaloisField.card 5 2 (by decide), Nat.card_zmod] at hc
  norm_num at hc

private abbrev G := ZMod 25 × ZMod 25
private def shear : G →+ G where
  toFun x := (x.1 + x.2, x.2)
  map_zero' := by simp
  map_add' x y := by ext <;> dsimp; abel

private def horizontal : AddSubgroup G := (AddMonoidHom.snd (ZMod 25) (ZMod 25)).ker

private def horizontalEquiv : ZMod 25 ≃ horizontal where
  toFun x := ⟨(x, 0), rfl⟩
  invFun x := x.val.1
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    exact Prod.ext rfl x.property.symm

-- A higher torsion level: the sharp lower bound is 25 fixed points in a 625 element group.
example : 25 ≤ Nat.card (shear - AddMonoidHom.id G).ker := by
  apply le_card_fixed_of_card_square shear horizontal (by decide)
  · rw [Nat.card_prod]
    norm_num [Nat.card_zmod]
  · exact (Nat.card_congr horizontalEquiv).symm.trans (Nat.card_zmod 25)
  · intro x
    change x.2 - x.2 = 0
    exact sub_self _

-- Absorption is necessary: negation on this odd-order group has only the zero fixed point.
example : ∃ x : G, (-AddMonoidHom.id G) x - x ∉ (⊥ : AddSubgroup G) := by
  refine ⟨(1, 0), ?_⟩
  change ¬ ((-(1 : ZMod 25) - 1, (0 : ZMod 25)) = 0)
  decide

-- An actual good elliptic curve over F_5, with 9 points including infinity.
private def W : WeierstrassCurve (ZMod 5) := ⟨0, 0, 0, 1, 1⟩
private instance : W.IsElliptic := (WeierstrassCurve.isElliptic_iff W).mpr
  (isUnit_iff_ne_zero.mpr (by decide +kernel))

example : Nat.card W.toAffine.Point = 9 := by
  let : DecidablePred (fun xy : ZMod 5 × ZMod 5 => W.toAffine.Equation xy.1 xy.2) := fun xy => by
    unfold WeierstrassCurve.Affine.Equation
    infer_instance
  let : Fintype {xy : ZMod 5 × ZMod 5 // W.toAffine.Equation xy.1 xy.2} := Subtype.fintype _
  rw [Nat.card_congr W.toAffine.pointEquiv]
  change Nat.card (Option {xy : ZMod 5 × ZMod 5 // W.toAffine.Equation xy.1 xy.2}) = 9
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_option, Fintype.card_subtype]
  have he : ({xy : ZMod 5 × ZMod 5 | W.toAffine.Equation xy.1 xy.2} : Finset _) =
      Finset.univ.filter (fun xy : ZMod 5 × ZMod 5 => xy.2 ^ 2 = xy.1 ^ 3 + xy.1 + 1) := by
    ext xy
    simp [WeierstrassCurve.Affine.equation_iff, W]
  rw [he]
  decide +kernel

example : 9 < 5 ^ 9 := by decide

#check DkMath.FLT.Frey.Source.residual_cofixed_point_count_tower_resonant_inertia_impossible

#print axioms FiniteFixedQuotient.card_le_card_fixed_mul
#print axioms FiniteFixedQuotient.le_card_fixed_of_card_square
#print axioms FiniteFieldFrobeniusFixed.exists_preimage_of_pow_card_eq
#print axioms EllipticFrobeniusFixedReduction.integerReduction
#print axioms EllipticFrobeniusFixedReduction.integerReduction_injOn_torsion
#print axioms EllipticFrobeniusFixedReduction.residue_pow_eq_of_frobenius_fixed
#print axioms EllipticFrobeniusFixedReduction.finitePointEmbedding
#print axioms EllipticFrobeniusFixedReduction.exists_finite_point_of_fixed_torsion
#print axioms EllipticFrobeniusFixedReduction.card_fixed_torsion_le_finite_points
#print axioms EllipticFrobeniusFixedReduction.torsion_index_le_finite_point_count_of_absorbing
#print axioms DkMath.FLT.Frey.Source.goodReductionPointCount_pos
#print axioms DkMath.FLT.Frey.Source.exists_good_prime_ne
#print axioms DkMath.FLT.Frey.Source.prime_power_pointAction_sub_mem_of_resonant_inertia
#print axioms DkMath.FLT.Frey.Source.residual_cofixed_point_count_tower_resonant_inertia_impossible

end DkMathTest.FLT.FreyGoodReductionTowerObstruction
