/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyWeilGeometry
import DkMath.Lib.NumberTheory.EllipticFunctionFieldPlaces
import DkMathTest.FLT.FreyResidualRepresentation

#print "file: DkMathTest.FLT.FreyWeilGeometry"

/-!
# NOTE-021: 実在する曲線の座標環・一般点・非自明な移動

ピタゴラスSource 2の同じ曲線を使う。点(0,0)は実際の非零2-torsionであり、
その平行移動は非恒等な関数体自己同型となり、二度合成すると恒等に戻る。
また定数点での座標環の評価は単射でないことを確認し、分数体への延長に必要な境界を検査する。
-/
namespace FreyWeilGeometryTest
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory
open EllipticFunctionField FreyResidualRepresentationTest
open scoped Polynomial.Bivariate
noncomputable section

local instance : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _
local instance : sample.rationalCurve.IsElliptic := sample.rationalCurve_isElliptic
local instance : (sample.rationalCurve⁄(AlgebraicClosure ℚ)).IsElliptic :=
  sample.geometricCurve_isElliptic

/-- 同じ実際の座標環のDedekind性。 -/
theorem actual_dedekind :
    IsDedekindDomain (sample.rationalCurve⁄(AlgebraicClosure ℚ)).CoordinateRing :=
  sample.geometricCoordinateRing_isDedekindDomain

local instance : (CoordinateRing.XYIdeal (sample.rationalCurve⁄(AlgebraicClosure ℚ))
    0 (C 0)).IsPrime :=
  (EllipticCoordinateRing.isMaximal_XYIdeal zero_coordinates_nonsingular.left).isPrime

/-- 具体的な有限点(0,0)での局所環はDVRである。 -/
theorem actual_local_dvr :
    IsDiscreteValuationRing (Localization.AtPrime
      (CoordinateRing.XYIdeal (sample.rationalCurve⁄(AlgebraicClosure ℚ)) 0 (C 0))) := by
  have := (EllipticCoordinateRing.isMaximal_XYIdeal zero_coordinates_nonsingular.left).isPrime
  exact EllipticCoordinateRing.isDiscreteValuationRing_localization_XYIdeal zero_coordinates_nonsingular

/-- 実際の一般点は、どの定数点にも等しくない。 -/
theorem actual_generic_not_constant (P : (sample.rationalCurve⁄(AlgebraicClosure ℚ)).Point) :
    genericPoint sample.rationalCurve (AlgebraicClosure ℚ) ≠
      Point.baseChange (AlgebraicClosure ℚ) _ P :=
  genericPoint_ne_baseChange _ _ P

/-- 同じ非零2-torsion点を、元の曲線の幾何学的点として読む。 -/
noncomputable def shiftPoint : (sample.rationalCurve⁄(AlgebraicClosure ℚ)).Point := twoPoint.val

/-- torsionの部分型を忘れても、同じ点は非零である。 -/
theorem shiftPoint_ne_zero : shiftPoint ≠ 0 := Point.some_ne_zero zero_coordinates_nonsingular

/-- 群法は同じ点の二倍零を保つ。 -/
theorem shiftPoint_add_self : shiftPoint + shiftPoint = 0 := by
  change twoPoint.val + twoPoint.val = 0
  rw [← two_nsmul]
  exact twoPoint.property

/-- 非零点の移動は非恒等な関数体自己同型を与える。 -/
theorem actual_translation_nonidentity :
    sample.functionFieldTranslation shiftPoint ≠ AlgEquiv.refl := by
  intro h
  apply shiftPoint_ne_zero
  apply sample.functionFieldTranslation_injective
  exact h.trans sample.functionFieldTranslation_zero.symm

/-- 実際の2-torsionによる移動を二度行うと恒等へ戻る。 -/
theorem actual_translation_square :
    (sample.functionFieldTranslation shiftPoint).trans
      (sample.functionFieldTranslation shiftPoint) = AlgEquiv.refl := by
  rw [← sample.functionFieldTranslation_add, shiftPoint_add_self, sample.functionFieldTranslation_zero]

/-- 引き戻しが一般点を実際に移すことを、同じ非零点について確認する。 -/
theorem actual_translation_moves_generic :
    Point.map (transEquiv sample.rationalCurve (AlgebraicClosure ℚ) shiftPoint :
      (sample.rationalCurve⁄(AlgebraicClosure ℚ)).FunctionField →ₐ[AlgebraicClosure ℚ]
        (sample.rationalCurve⁄(AlgebraicClosure ℚ)).FunctionField)
      (genericPoint sample.rationalCurve (AlgebraicClosure ℚ)) =
      genericPoint sample.rationalCurve (AlgebraicClosure ℚ) +
        Point.baseChange (AlgebraicClosure ℚ) _ shiftPoint :=
  map_transEquiv_genericPoint _ _ _

/-- (0,0)への評価は非零のX類を消す。定数点への評価を関数体の埋め込みとは扱えない。 -/
theorem constant_evaluation_not_injective :
    ¬ Function.Injective (evalAt sample.rationalCurve (AlgebraicClosure ℚ)
      zero_coordinates_nonsingular.left) := by
  intro hinj
  apply CoordinateRing.XClass_ne_zero (W' := sample.rationalCurve⁄(AlgebraicClosure ℚ)) 0
  apply hinj
  rw [map_zero, CoordinateRing.XClass, evalAt_mk]
  simp only [evalEval_C, eval_sub, eval_X, eval_C, sub_self]

/-- 同じ有限点に対応する場所は非零素イデアルである。 -/
theorem actual_place_nonzero :
    (placeOf sample.rationalCurve (AlgebraicClosure ℚ) shiftPoint shiftPoint_ne_zero).asIdeal ≠ ⊥ :=
  (placeOf _ _ _ shiftPoint_ne_zero).ne_bot

/-- 全ての有限場所は、同じ曲線の有限点から得られる。 -/
theorem actual_places_covered
    (v : IsDedekindDomain.HeightOneSpectrum
      (sample.rationalCurve⁄(AlgebraicClosure ℚ)).CoordinateRing) :
    ∃ (P : (sample.rationalCurve⁄(AlgebraicClosure ℚ)).Point) (hP : P ≠ 0),
      placeOf sample.rationalCurve (AlgebraicClosure ℚ) P hP = v :=
  placeOf_surjective _ _ v

end

end FreyWeilGeometryTest
