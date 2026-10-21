/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_WeierstrassCurve_Affine_FunctionField_adjoin_X_Y_eq_top.lean.
Upstream blob: a38b593248665652d1fcca051b48c11068c35a8f
Modified for DkMath: actual guarded natural-number pullback; textbook APIs and existing geometry.
-/

import DkMath.Lib.NumberTheory.EllipticFunctionField
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

#print "file: DkMath.Lib.NumberTheory.EllipticFunctionFieldGenerators"

/-!
# 二つの一般座標による生成

座標環は多項式の類、関数体はその分数である。従って生成元x,yを含む中間体は全体になる。
-/

namespace DkMath.Lib.NumberTheory.EllipticFunctionField
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
variable {K : Type*} [Field K] (W : WeierstrassCurve K)

/-- 座標環は、二つの実際の座標類X,Yで代数として生成される。 -/
theorem coordinateRing_adjoin_X_Y :
    Algebra.adjoin K {CoordinateRing.mk W.toAffine (C X), CoordinateRing.mk W.toAffine Y} = ⊤ := by
  set x := CoordinateRing.mk W.toAffine (C X) with hx
  set y := CoordinateRing.mk W.toAffine Y with hy
  apply Algebra.eq_top_iff.mpr
  intro r
  induction r using AdjoinRoot.induction_on with
  | ih p =>
    have hC : ∀ c : K[X], CoordinateRing.mk W.toAffine (C c) ∈ Algebra.adjoin K {x, y} := by
      intro c
      have : CoordinateRing.mk W.toAffine (C c) = aeval x c := by
        have h1 : (CoordinateRing.mk W.toAffine).comp C = (aeval x : K[X] →ₐ[K] _).toRingHom := by
          apply Polynomial.ringHom_ext
          · intro k
            rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_C]
            rfl
          · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X]
        exact congrArg (fun f : K[X] →+* _ => f c) h1
      rw [this]
      exact Algebra.adjoin_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
        (Polynomial.aeval_mem_adjoin_singleton K x)
    induction p using Polynomial.induction_on with
    | C c => exact hC c
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | monomial n c _ =>
      rw [map_mul, map_pow]
      exact mul_mem (hC c)
        (pow_mem (Algebra.subset_adjoin (Set.mem_insert_of_mem x (Set.mem_singleton y))) _)

/-- 関数体は一般座標x,yで体として生成される。分数体の各元を分子・分母へ分解する。 -/
theorem functionField_adjoin_X_Y : IntermediateField.adjoin K {algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (Polynomial.C Polynomial.X)), algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine Polynomial.X)} = ⊤ := by
  set x := CoordinateRing.mk W.toAffine (C X)
  set y := CoordinateRing.mk W.toAffine Y
  set S : IntermediateField K W.toAffine.FunctionField := IntermediateField.adjoin K
    {algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField x,
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField y} with hS
  have hR : ∀ r : W.toAffine.CoordinateRing,
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField r ∈ S := by
    intro r
    let φ : W.toAffine.CoordinateRing →ₐ[K] W.toAffine.FunctionField :=
      IsScalarTower.toAlgHom K W.toAffine.CoordinateRing W.toAffine.FunctionField
    have hr : r ∈ (⊤ : Subalgebra K W.toAffine.CoordinateRing) := Algebra.mem_top
    rw [← coordinateRing_adjoin_X_Y W] at hr
    have himg : φ r ∈ (Algebra.adjoin K {x, y}).map φ := Subalgebra.mem_map.mpr ⟨r, hr, rfl⟩
    rw [AlgHom.map_adjoin] at himg
    have hle : Algebra.adjoin K (φ '' {x, y}) ≤ S.toSubalgebra := by
      rw [Set.image_pair]
      exact IntermediateField.algebra_adjoin_le_adjoin K _
    exact hle himg
  apply eq_top_iff.mpr
  intro z _
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := W.toAffine.CoordinateRing) z
  exact div_mem (hR a) (hR b)


end DkMath.Lib.NumberTheory.EllipticFunctionField
