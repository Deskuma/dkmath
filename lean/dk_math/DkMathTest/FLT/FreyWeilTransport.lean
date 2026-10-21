/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyWeilTransport
import DkMathTest.FLT.FreyWeilValuation

#print "file: DkMathTest.FLT.FreyWeilTransport"

/-!
# NOTE-024: 実在するSourceの次数・無限遠点・移動の回帰
指数2では非零目標の次数4と零目標の次数3を区別する。
同じ非零2-torsion点Tで2T=Oとなる例外輸送と、Oを移動元にする逆方向も検査する。
2R=Tの点Rでは通常輸送が働く。37倍も多項式を展開せずファイバーの計数だけで検査する。
-/
namespace FreyWeilTransportTest
open Polynomial WeierstrassCurve WeierstrassCurve.Affine WithZero
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open DkMath.Lib.NumberTheory.EllipticFunctionField
open FreyResidualRepresentationTest FreyWeilFunctionTest FreyWeilValuationTest
local instance : sample.rationalCurve.IsElliptic := sample.rationalCurve_isElliptic
local notation "E" => sample.rationalCurve

open Classical in
/-- 非零目標のファイバーは4点とも有限点である。 -/
theorem normDegree_nonzero_target :
    ((Algebra.norm (AlgebraicClosure ℚ)[X] (weilNumerator E 2 (by decide) twoPoint.val target_two_killed)).natDegree : ℤ) = 4 := by
  rw [sample.curve_weilNumerator_normDegree]
  simp [twoPoint_ne_zero]

open Classical in
/-- 零目標では4点のうちOだけを除き、次数3となる。 -/
theorem normDegree_zero_target :
    ((Algebra.norm (AlgebraicClosure ℚ)[X] (weilNumerator E 2 (by decide) 0 (smul_zero _))).natDegree : ℤ) = 3 := by
  rw [normDegree_weilNumerator]
  norm_num

open Classical in
/-- 指数1の零ファイバーはOだけで、有限点の寄与は0。 -/
theorem normDegree_one :
    ((Algebra.norm (AlgebraicClosure ℚ)[X] (weilNumerator E 1 (by decide) 0 (smul_zero _))).natDegree : ℤ) = 0 := by
  rw [normDegree_weilNumerator]
  norm_num

open Classical in
/-- 指数37でも有限点の計数は37²−1=1368。展開計算は不要。 -/
theorem normDegree_thirtySeven :
    ((Algebra.norm (AlgebraicClosure ℚ)[X] (weilNumerator E 37 (by decide) 0 (smul_zero _))).natDegree : ℤ) = 1368 := by
  rw [normDegree_weilNumerator]
  norm_num

open Classical in
/-- 非零目標の分子のOでの位数は−4。 -/
theorem numerator_infinity_order :
    infinityOrder E (numerator 2 (by decide) twoPoint.val target_two_killed)
      (numerator_ne_zero 2 (by decide) twoPoint.val target_two_killed) = -4 := by
  change infinityOrder E (algebraMap (sample.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).CoordinateRing
    (sample.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField _) _ = _
  rw [infinityOrder_weilNumerator]
  simp [twoPoint_ne_zero]

open Classical in
/-- 分子と分母の次数差は、同じ商のOでの一重極となる。 -/
theorem actual_infinity_pole :
    pointOrder E 0 (sample.curve_weilFunction 2 (by decide) twoPoint.val target_two_killed)
      (sample.curve_weilFunction_ne_zero 2 (by decide) twoPoint.val target_two_killed) = -1 := by
  rw [sample.curve_weilFunction_pointOrder]
  simp [Ne.symm twoPoint_val_ne_zero]

open Classical in
/-- 零目標ではOでも分子と分母が相殺する。 -/
theorem infinity_zero_target_cancels :
    infinityOrder E (weilFunction E 2 (by decide) 0 (smul_zero _))
      (weilFunction_ne_zero E 2 (by decide) 0 (smul_zero _)) = 0 := by
  rw [infinityOrder_weilFunction]
  simp

open Classical in
/-- 同じTの自己和はOであり、例外輸送の条件を実際に満たす。 -/
theorem target_add_self : (twoPoint.val : Points E) + twoPoint.val = 0 := by
  simpa only [two_smul] using target_two_killed

open Classical in
/-- TでTだけ移動すると、移動先Oの一重極がそのまま現れる。 -/
theorem exceptional_translation_pole :
    pointOrder E twoPoint.val
      (transEquiv E (AlgebraicClosure ℚ) twoPoint.val (weilFunction E 2 (by decide) twoPoint.val target_two_killed))
      ((transEquiv E (AlgebraicClosure ℚ) twoPoint.val).toRingEquiv.map_ne_zero_iff.mpr
        (weilFunction_ne_zero E 2 (by decide) twoPoint.val target_two_killed)) = -1 := by
  rw [pointOrder_transEquiv_weilFunction, target_add_self]
  simp [Ne.symm twoPoint_val_ne_zero]

open Classical in
/-- Oを移動元にした場合にも、同じTの極が輸送される。 -/
theorem infinity_translation_pole :
    pointOrder E 0
      (transEquiv E (AlgebraicClosure ℚ) twoPoint.val (weilFunction E 2 (by decide) twoPoint.val target_two_killed))
      ((transEquiv E (AlgebraicClosure ℚ) twoPoint.val).toRingEquiv.map_ne_zero_iff.mpr
        (weilFunction_ne_zero E 2 (by decide) twoPoint.val target_two_killed)) = -1 := by
  rw [pointOrder_transEquiv_weilFunction]
  simp [target_two_killed, Ne.symm twoPoint_val_ne_zero]

open Classical in
/-- 通常の有限点Rでは、2-torsion移動後にも一重零点が残る。 -/
theorem regular_translation_zero :
    pointOrder E fourPoint
      (transEquiv E (AlgebraicClosure ℚ) twoPoint.val (weilFunction E 2 (by decide) twoPoint.val target_two_killed))
      ((transEquiv E (AlgebraicClosure ℚ) twoPoint.val).toRingEquiv.map_ne_zero_iff.mpr
        (weilFunction_ne_zero E 2 (by decide) twoPoint.val target_two_killed)) = 1 := by
  rw [pointOrder_transEquiv_weilFunction]
  simp [smul_add, fourPoint_double, target_two_killed, twoPoint_ne_zero]

open Classical in
/-- Source入口でも、任意の点の位数保存へ同じ実際の2-torsion点を渡せる。 -/
theorem source_translation_invariance (P : Points E) :
    pointOrder E P
      (transEquiv E (AlgebraicClosure ℚ) twoPoint.val (sample.curve_weilFunction 2 (by decide) twoPoint.val target_two_killed))
      ((transEquiv E (AlgebraicClosure ℚ) twoPoint.val).toRingEquiv.map_ne_zero_iff.mpr
        (sample.curve_weilFunction_ne_zero 2 (by decide) twoPoint.val target_two_killed)) =
      pointOrder E P (sample.curve_weilFunction 2 (by decide) twoPoint.val target_two_killed)
        (sample.curve_weilFunction_ne_zero 2 (by decide) twoPoint.val target_two_killed) :=
  sample.curve_weilFunction_pointOrder_transEquiv 2 (by decide) twoPoint.val target_two_killed P twoPoint.val target_two_killed

end FreyWeilTransportTest
