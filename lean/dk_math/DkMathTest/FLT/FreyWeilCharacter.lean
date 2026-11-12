/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyWeilCharacter
import DkMathTest.FLT.FreyWeilTransport

#print "file: DkMathTest.FLT.FreyWeilCharacter"

/-!
# NOTE-025: 実在する曲線の比例定数と片側の指標
Source 2=(4,3,5)の同じ曲線と非零2-torsion目標Tを使用する。
定数2の復元、実際の移動固有方程式、その一意性、定数倍の不変性を回帰する。
移動T+T=Oはc(T,T)²=1を与えるが、交代性c(T,T)=1はここでは結論しない。
指数1と37の零目標も境界例として扱い、巨大な式を展開しない。
-/
namespace FreyWeilCharacterTest
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open DkMath.Lib.NumberTheory.EllipticFunctionField
open DkMath.Lib.NumberTheory.EllipticFunctionFieldConstants
open FreyResidualRepresentationTest FreyWeilFunctionTest FreyWeilValuationTest
local instance : sample.rationalCurve.IsElliptic := sample.rationalCurve_isElliptic
local instance : IsDedekindDomain (sample.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).CoordinateRing :=
  geometricCoordinateRing_isDedekindDomain _
local notation "E" => sample.rationalCurve

/-- 同じ実在する非零点を、一般n-torsion入口の型で固定する。 -/
noncomputable def target : Torsion E 2 := ⟨twoPoint.val, target_two_killed⟩

/-- 目標が零点だけの空虚な回帰ではないことを記録する。 -/
theorem target_ne_zero : target ≠ 0 := by
  intro h
  exact twoPoint_val_ne_zero (congrArg Subtype.val h)

/-- 座標環の定数2は単元である。ノルム次数による定数判定を実際の曲線へ適用する。 -/
theorem coordinate_constant_unit :
    IsUnit (algebraMap (AlgebraicClosure ℚ) (sample.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).CoordinateRing 2) := by
  apply (isUnit_iff_eq_algebraMap (sample.rationalCurve.baseChange (AlgebraicClosure ℚ)) _).mpr
  exact ⟨2, by norm_num, rfl⟩

/-- 定数2は全ての有限場所で付値1となる。 -/
theorem constant_two_valuations
    (v : IsDedekindDomain.HeightOneSpectrum (sample.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).CoordinateRing) :
    v.valuation (sample.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField
      (algebraMap (AlgebraicClosure ℚ) (sample.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField 2) = 1 := by
  classical
  obtain ⟨P, hP, rfl⟩ := placeOf_surjective E (AlgebraicClosure ℚ) v
  exact valuation_algebraMap_eq_one E (AlgebraicClosure ℚ) P hP (by norm_num)

/-- 同じ関数体の定数2を、全有限付値の条件だけから一意な単元として復元できる。 -/
theorem recover_constant_two :
    ∃! c : (AlgebraicClosure ℚ)ˣ,
      algebraMap (AlgebraicClosure ℚ) (sample.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField 2 =
        algebraMap (AlgebraicClosure ℚ) (sample.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField
          (c : AlgebraicClosure ℚ) := by
  apply existsUnique_unit_of_valuation_eq_one (sample.rationalCurve.baseChange (AlgebraicClosure ℚ)) _ constant_two_valuations
  exact (_root_.map_ne_zero _).mpr (by norm_num)

open Classical in
/-- 同じSourceの既存の候補関数に対し、実際の移動固有方程式が成立する。 -/
theorem actual_translation_eigenvalue :
    transEquiv E (AlgebraicClosure ℚ) target.val
      (sample.curve_weilFunction 2 (by decide) target.val target.property) =
      algebraMap (AlgebraicClosure ℚ) (sample.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField
        (sample.curve_weilTranslationUnit 2 (by decide) target target : AlgebraicClosure ℚ) *
          sample.curve_weilFunction 2 (by decide) target.val target.property :=
  sample.curve_weilTranslationUnit_spec 2 (by decide) target target

open Classical in
/-- 同じ非零目標の固有値が、任意の候補単元に対して一意であることを回帰する。 -/
theorem actual_translation_unique (c : (AlgebraicClosure ℚ)ˣ)
    (hc : transEquiv E (AlgebraicClosure ℚ) target.val
      (weilFunction E 2 (by decide) target.val target.property) =
      algebraMap (AlgebraicClosure ℚ) (sample.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField
        (c : AlgebraicClosure ℚ) * weilFunction E 2 (by decide) target.val target.property) :
    c = weilTranslationUnit E 2 (by decide) target target :=
  weilTranslationUnit_unique E 2 (by decide) target target c hc

/-- 取り出した比例定数は非零単元のままであり、二乗は1である。 -/
theorem actual_translation_square :
    sample.curve_weilTranslationUnit 2 (by decide) target target ^ 2 = 1 :=
  sample.curve_weilTranslationUnit_pow 2 (by decide) target target

/-- 非零目標でも零移動の値は1。 -/
theorem zero_translation : weilTranslationUnit E 2 (by decide) target 0 = 1 :=
  weilTranslationUnit_zero E 2 (by decide) target

/-- 同じ二つの移動の合成を、比例定数の積として回帰する。 -/
theorem actual_translation_multiplicative :
    weilTranslationUnit E 2 (by decide) target (target + target) =
      weilTranslationUnit E 2 (by decide) target target * weilTranslationUnit E 2 (by decide) target target :=
  weilTranslationUnit_add E 2 (by decide) target target target

/-- μ₂に値を持つ指標を実際に構成し、値の二乗が1であることを型からも取り出す。 -/
theorem root_character_square :
    (sample.curve_weilTranslationCharacter 2 (by decide) target target).val ^ 2 = 1 :=
  (mem_rootsOfUnity 2 _).mp (sample.curve_weilTranslationCharacter 2 (by decide) target target).property

/-- 標準のAddCharの加法則が、同じSourceの実際の指標に適用できる。 -/
theorem source_character_add (Q R : Torsion E 2) :
    sample.curve_weilTranslationCharacter 2 (by decide) target (Q + R) =
      sample.curve_weilTranslationCharacter 2 (by decide) target Q *
        sample.curve_weilTranslationCharacter 2 (by decide) target R :=
  AddChar.map_add_eq_mul _ Q R

open Classical in
/-- 非零定数2倍した同じWeil関数にも、同じ固有値が現れる。 -/
theorem scaled_function_eigenvalue :
    transEquiv E (AlgebraicClosure ℚ) target.val
      (algebraMap (AlgebraicClosure ℚ) (sample.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField
        (2 : AlgebraicClosure ℚ) * weilFunction E 2 (by decide) target.val target.property) =
      algebraMap (AlgebraicClosure ℚ) (sample.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField
        (weilTranslationUnit E 2 (by decide) target target : AlgebraicClosure ℚ) *
        (algebraMap (AlgebraicClosure ℚ) (sample.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField
          (2 : AlgebraicClosure ℚ) * weilFunction E 2 (by decide) target.val target.property) :=
  weilTranslationUnit_const_mul_spec E 2 (by decide) target target (Units.mk0 2 (by norm_num))

/-- 零目標では移動しても関数1のままで、比例定数は1である。 -/
theorem zero_target_unit : weilTranslationUnit E 2 (by decide) 0 target = 1 :=
  weilTranslationUnit_zero_target E 2 (by decide) target

/-- 指数1でも同じ構成の零移動は1。 -/
theorem exponent_one : weilTranslationUnit E 1 (by decide) 0 0 = 1 :=
  weilTranslationUnit_zero E 1 (by decide) 0

/-- 指数37の零目標でも、全ての移動で比例定数は1となる。 -/
theorem exponent_thirtySeven (Q : Torsion E 37) : weilTranslationUnit E 37 (by decide) 0 Q = 1 :=
  weilTranslationUnit_zero_target E 37 (by decide) Q

end FreyWeilCharacterTest
