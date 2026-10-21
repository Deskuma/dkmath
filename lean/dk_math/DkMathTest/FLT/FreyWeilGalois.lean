/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyWeilGalois
import DkMathTest.FLT.FreyWeilBicharacter

#print "file: DkMathTest.FLT.FreyWeilGalois"

/-!
# NOTE-027: 同じ実際の曲線でガロア同変性を測る

任意の絶対ガロア群元を使うため、恒等写像への特殊化だけではない。
非零の二つの有理2-torsion点が固定される事実と、同じ非対角の値の係数作用を接続する。
値が非自明であることや、非自明な自己同型の存在をこの回帰から結論しない。
-/
namespace FreyWeilGaloisTest
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open DkMath.Lib.NumberTheory.EllipticFunctionField
open FreyResidualRepresentationTest FreyWeilCharacterTest FreyWeilBicharacterTest FreyWeilValuationTest
local instance : sample.rationalCurve.IsElliptic := sample.rationalCurve_isElliptic
attribute [local instance] geometricCoordinateRing_isDedekindDomain
local notation "E" => sample.rationalCurve

/-- (0,0)は係数作用で固定される実際の非零torsion点である。 -/
theorem target_fixed (σ : Field.absoluteGaloisGroup ℚ) : torsionAction E 2 σ target = target :=
  twoPoint_fixed σ

/-- (4,−2)も有理座標を持つため、任意のガロア群元で固定される。 -/
theorem other_fixed (σ : Field.absoluteGaloisGroup ℚ) : torsionAction E 2 σ otherTarget = otherTarget := by
  apply Subtype.ext
  change Point.some (σ.toAlgHom 4) (σ.toAlgHom (-2)) _ = Point.some 4 (-2) _
  simp only [map_ofNat, map_neg]

/-- 一般の係数に対する半線形性を測る。係数体上の線形性とは異なる式である。 -/
theorem actual_semilinear (σ : Field.absoluteGaloisGroup ℚ) (a : AlgebraicClosure ℚ)
    (f : (sample.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField) :
    (galFunctionFieldEquiv E σ).toRingHom (algebraMap (AlgebraicClosure ℚ) _ a * f) =
      algebraMap (AlgebraicClosure ℚ) _ (σ.toAlgHom a) * (galFunctionFieldEquiv E σ).toRingHom f :=
  galFunctionFieldEquiv_const_mul E σ a f

/-- 一般点のx座標は係数作用で変わらない。 -/
theorem generic_x_fixed (σ : Field.absoluteGaloisGroup ℚ) :
    (galFunctionFieldEquiv E σ).toRingHom (genericX E (AlgebraicClosure ℚ)) =
      genericX E (AlgebraicClosure ℚ) := gal_genericX E σ

/-- 一般点のy座標も固定される。 -/
theorem generic_y_fixed (σ : Field.absoluteGaloisGroup ℚ) :
    (galFunctionFieldEquiv E σ).toRingHom (genericY E (AlgebraicClosure ℚ)) =
      genericY E (AlgebraicClosure ℚ) := gal_genericY E σ

open Classical in
/-- 実際の非零移動点と任意の関数で、平行移動との交換則を測る。 -/
theorem actual_translation (σ : Field.absoluteGaloisGroup ℚ)
    (f : (sample.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField) :
    (galFunctionFieldEquiv E σ).toRingHom (transEquiv E (AlgebraicClosure ℚ) target.val f) =
      transEquiv E (AlgebraicClosure ℚ) (pointAction E σ target.val)
        ((galFunctionFieldEquiv E σ).toRingHom f) := gal_transEquiv E σ target.val f

/-- ゼロ関数を含む全ての関数について、実際の有限点の付値を輸送する。 -/
theorem actual_finite_valuation (σ : Field.absoluteGaloisGroup ℚ)
    (f : (sample.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField) :
    finitePointValuation E (pointAction E σ target.val) (pointAction_ne_zero E σ twoPoint_val_ne_zero)
        (galFunctionFieldEquiv E σ f) = finitePointValuation E target.val twoPoint_val_ne_zero f :=
  finitePointValuation_galois E σ target.val twoPoint_val_ne_zero f

/-- 選択されたWeil関数が不変とは言わず、一意な非零定数倍を回帰する。 -/
theorem actual_generator_scalar (σ : Field.absoluteGaloisGroup ℚ) :
    ∃! a : (AlgebraicClosure ℚ)ˣ,
      galFunctionFieldEquiv E σ (weilFunction E 2 (by decide) target.val target.property) =
        algebraMap (AlgebraicClosure ℚ) (sample.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField (a : AlgebraicClosure ℚ) *
          weilFunction E 2 (by decide) (torsionAction E 2 σ target).val (torsionAction E 2 σ target).property :=
  existsUnique_scalar_galois_weilFunction E 2 (by decide) σ target

/-- 対角以外の同じ比例定数の同変性。 -/
theorem actual_unit_galois (σ : Field.absoluteGaloisGroup ℚ) :
    sample.curve_weilTranslationUnit 2 (by decide) (torsionAction E 2 σ otherTarget) (torsionAction E 2 σ target) =
      galoisUnitMap σ (sample.curve_weilTranslationUnit 2 (by decide) otherTarget target) :=
  sample.curve_weilTranslationUnit_galois 2 (by decide) σ target otherTarget

/-- 有理点二つが固定されるので、同じ非対角の比例定数も係数作用で固定される。 -/
theorem actual_unit_fixed (σ : Field.absoluteGaloisGroup ℚ) :
    galoisUnitMap σ (sample.curve_weilTranslationUnit 2 (by decide) otherTarget target) =
      sample.curve_weilTranslationUnit 2 (by decide) otherTarget target := by
  have h := actual_unit_galois σ
  rw [target_fixed, other_fixed] at h
  exact h.symm

/-- μ₂に値を持つ双指標の、同じ非対角値の同変性。 -/
theorem actual_bicharacter_galois (σ : Field.absoluteGaloisGroup ℚ) :
    sample.curve_weilAlternatingBicharacter 2 (by decide) (torsionAction E 2 σ target) (torsionAction E 2 σ otherTarget) =
      galoisRootMap 2 σ (sample.curve_weilAlternatingBicharacter 2 (by decide) target otherTarget) :=
  sample.curve_weilAlternatingBicharacter_galois 2 (by decide) σ target otherTarget

/-- 同じ結論は既存の剰余表現のAPIからも到達できる。 -/
theorem actual_residual_galois (σ : Field.absoluteGaloisGroup ℚ) :
    sample.curve_weilAlternatingBicharacter 2 (by decide) (sample.residualRepresentation σ target)
        (sample.residualRepresentation σ otherTarget) =
      galoisRootMap 2 σ (sample.curve_weilAlternatingBicharacter 2 (by decide) target otherTarget) :=
  sample.curve_weilAlternatingBicharacter_residual (by decide) σ target otherTarget

/-- 大きな指数37でも展開せず同じ一般定理を使える。 -/
theorem exponent_thirtySeven (σ : Field.absoluteGaloisGroup ℚ) (Q T : Torsion E 37) :
    weilAlternatingBicharacter E 37 (by decide) (torsionAction E 37 σ Q) (torsionAction E 37 σ T) =
      galoisRootMap 37 σ (weilAlternatingBicharacter E 37 (by decide) Q T) :=
  weilAlternatingBicharacter_galois E 37 (by decide) σ Q T

/-- 指数1の境界でも、根への係数作用は単位元を保つ。 -/
theorem exponent_one (σ : Field.absoluteGaloisGroup ℚ) :
    galoisRootMap 1 σ (weilAlternatingBicharacter E 1 (by decide) 0 0) = 1 := by
  rw [weilAlternatingBicharacter_self, map_one]

end FreyWeilGaloisTest
