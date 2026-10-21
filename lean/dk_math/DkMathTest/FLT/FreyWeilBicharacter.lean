/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyWeilBicharacter
import DkMathTest.FLT.FreyWeilCharacter

#print "file: DkMathTest.FLT.FreyWeilBicharacter"

/-!
# NOTE-026: 二つの異なる実際の2-torsion点で交代的双指標を検査する

Source 2の正規化モデルy²+xy=x³−2x²−9xには、T=(0,0)に加えR=(4,−2)がある。
Rの非特異性・非零性・二倍零・Tとの相異性を証明し、対角だけでない右加法性と交換則を回帰する。
2U=Tとなる既存の点Uでの軌道積を、Oと有限点の両方で測る。
非退化性や対の値の非自明性を、この回帰から結論することはない。
-/
namespace FreyWeilBicharacterTest
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open DkMath.Lib.NumberTheory.EllipticFunctionField
open DkMath.Lib.NumberTheory.FreyGapCubic
open DkMath.FLT.Frey
open FreyResidualRepresentationTest FreyWeilFunctionTest FreyWeilCharacterTest
local instance : sample.rationalCurve.IsElliptic := sample.rationalCurve_isElliptic
local notation "E" => sample.rationalCurve

/-- 別の実際の有理座標点(4,−2)は、同じ曲線上で非特異である。 -/
theorem other_coordinates_nonsingular :
    (sample.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).Nonsingular 4 (-2) := by
  norm_num [nonsingular_iff', equation_iff, Source.rationalCurve, sample, normalized,
    WeierstrassCurve.baseChange, WeierstrassCurve.map]

/-- 同じ正規化モデルのもう一つの実際の非零2-torsion点。 -/
noncomputable def otherTarget : Torsion E 2 := by
  classical
  refine ⟨Point.some 4 (-2) other_coordinates_nonsingular, ?_⟩
  change 2 • (Point.some 4 (-2) other_coordinates_nonsingular : Points E) = 0
  rw [two_nsmul]
  apply Point.add_self_of_Y_eq
  norm_num [negY, Source.rationalCurve, sample, normalized,
    WeierstrassCurve.baseChange, WeierstrassCurve.map]

/-- 新しい点はOではない。 -/
theorem otherTarget_ne_zero : otherTarget ≠ 0 := by
  intro h
  have he := congrArg Subtype.val h
  exact Point.some_ne_zero other_coordinates_nonsingular he

/-- 二つの回帰点はx座標が4と0なので異なる。 -/
theorem otherTarget_ne_target : otherTarget ≠ target := by
  intro h
  have he := congrArg (fun Q : Torsion E 2 => Point.xc Q.val) h
  change (4 : AlgebraicClosure ℚ) = 0 at he
  norm_num at he

/-- 実際の二倍零の条件を、倍写像の等式として固定する。 -/
theorem target_double : 2 • target.val = 0 := target.property

/-- 既存の2倍原像Uから作る、同じWeil関数の二項軌道積。 -/
noncomputable def actualOrbit : (sample.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField :=
  weilTranslateOrbitProduct E 2 (by decide) target.val target_double fourPoint

/-- 測定する積の全因子が非零なので、積も非零である。 -/
theorem actualOrbit_ne_zero : actualOrbit ≠ 0 :=
  weilTranslateOrbitProduct_ne_zero E 2 (by decide) target.val target_double fourPoint

/-- Oにおいても軌道積の位数は0である。 -/
theorem orbit_order_at_infinity : pointOrder E 0 actualOrbit actualOrbit_ne_zero = 0 :=
  pointOrder_weilTranslateOrbitProduct E 2 (by decide) target.val target_double fourPoint fourPoint_double 0

/-- 同じ積の位数は、実在する有限点Uにおいても0である。 -/
theorem orbit_order_at_finite_point : pointOrder E fourPoint actualOrbit actualOrbit_ne_zero = 0 :=
  pointOrder_weilTranslateOrbitProduct E 2 (by decide) target.val target_double fourPoint fourPoint_double fourPoint

/-- 軌道積の定数性は、全点の位数から一意な非零単元として復元される。 -/
theorem actualOrbit_is_constant :
    ∃! a : (AlgebraicClosure ℚ)ˣ, actualOrbit =
      algebraMap (AlgebraicClosure ℚ) (sample.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField (a : AlgebraicClosure ℚ) :=
  existsUnique_unit_weilTranslateOrbitProduct E 2 (by decide) target.val target_double fourPoint fourPoint_double

open Classical in
/-- 非零目標自身による移動が、実際の同じ関数を固定する。 -/
theorem actual_self_translation :
    transEquiv E (AlgebraicClosure ℚ) target.val (weilFunction E 2 (by decide) target.val target_double) =
      weilFunction E 2 (by decide) target.val target_double :=
  transEquiv_weilFunction_self E 2 (by decide) target.val target_double

/-- 前章の二乗1から進み、非零目標の対角値そのものが1となる。 -/
theorem actual_self_unit : sample.curve_weilTranslationUnit 2 (by decide) target target = 1 :=
  sample.curve_weilTranslationUnit_self 2 (by decide) target

/-- 別の非零目標でも、同じ構成の対角値は1である。 -/
theorem other_self_unit : sample.curve_weilTranslationUnit 2 (by decide) otherTarget otherTarget = 1 :=
  sample.curve_weilTranslationUnit_self 2 (by decide) otherTarget

/-- 異なる二つの目標の和について、同じSourceの右加法性を測る。 -/
theorem actual_add_right :
    sample.curve_weilTranslationUnit 2 (by decide) (target + otherTarget) target =
      sample.curve_weilTranslationUnit 2 (by decide) target target *
        sample.curve_weilTranslationUnit 2 (by decide) otherTarget target :=
  sample.curve_weilTranslationUnit_add_right 2 (by decide) target target otherTarget

/-- 対角以外の二点を交換すると、同じSourceの比例定数は逆元となる。 -/
theorem actual_swap :
    sample.curve_weilTranslationUnit 2 (by decide) otherTarget target =
      (sample.curve_weilTranslationUnit 2 (by decide) target otherTarget)⁻¹ :=
  sample.curve_weilTranslationUnit_swap 2 (by decide) target otherTarget

/-- 目標を動かす標準のAddCharにも右加法性が入っている。 -/
theorem right_character_add (T R : Torsion E 2) :
    weilTranslationRightCharacter E 2 (by decide) target (T + R) =
      weilTranslationRightCharacter E 2 (by decide) target T * weilTranslationRightCharacter E 2 (by decide) target R :=
  AddChar.map_add_eq_mul _ T R

/-- 構成した双指標の値は、前章の同じSourceの比例定数である。 -/
theorem actual_bicharacter_value :
    (sample.curve_weilAlternatingBicharacter 2 (by decide) target otherTarget).val =
      sample.curve_weilTranslationUnit 2 (by decide) otherTarget target := rfl

/-- 双指標の外側の加法則。 -/
theorem bicharacter_add_left (S R T : Torsion E 2) :
    sample.curve_weilAlternatingBicharacter 2 (by decide) (S + R) T =
      sample.curve_weilAlternatingBicharacter 2 (by decide) S T *
        sample.curve_weilAlternatingBicharacter 2 (by decide) R T := by
  exact congrArg (fun f => f T) (AddChar.map_add_eq_mul
    (sample.curve_weilAlternatingBicharacter 2 (by decide)) S R)

/-- μ₂の中でも対角上の値は1である。 -/
theorem bicharacter_self : sample.curve_weilAlternatingBicharacter 2 (by decide) target target = 1 :=
  weilAlternatingBicharacter_self E 2 (by decide) target

/-- μ₂の中での交換則。 -/
theorem bicharacter_swap : sample.curve_weilAlternatingBicharacter 2 (by decide) target otherTarget =
    (sample.curve_weilAlternatingBicharacter 2 (by decide) otherTarget target)⁻¹ :=
  weilAlternatingBicharacter_swap E 2 (by decide) target otherTarget

/-- 指数1でも交代性の同じ入口が働く。 -/
theorem exponent_one : weilAlternatingBicharacter E 1 (by decide) 0 0 = 1 :=
  weilAlternatingBicharacter_self E 1 (by decide) 0

/-- 指数37でも、有限積を展開せず一般の交代性を特殊化できる。 -/
theorem exponent_thirtySeven (T : Torsion E 37) : weilAlternatingBicharacter E 37 (by decide) T T = 1 :=
  weilAlternatingBicharacter_self E 37 (by decide) T

end FreyWeilBicharacterTest
