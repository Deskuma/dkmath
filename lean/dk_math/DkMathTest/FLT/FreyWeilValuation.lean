/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyWeilValuation
import DkMathTest.FLT.FreyWeilFunction

#print "file: DkMathTest.FLT.FreyWeilValuation"

/-!
# NOTE-023: 同じ実在する曲線の一重零点・一重極・相殺

Source 2の非零2-torsion Tと、2R=Tとなる同じ曲線の点Rを使う。
Rでは分子が一重に消えて商の位数は+1。Tでは分母だけが一重に消え、商の位数は−1となる。
さらに2Q=Rの点を選ぶと、Qは両ファイバーの外で位数0になる。
目標Oでの分子・分母の相殺、指数1、37倍の非零点での測定も検査する。
-/
namespace FreyWeilValuationTest
open WeierstrassCurve WeierstrassCurve.Affine WithZero
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open FreyResidualRepresentationTest FreyWeilFunctionTest
local instance : sample.rationalCurve.IsElliptic := sample.rationalCurve_isElliptic
local notation "E" => sample.rationalCurve

/-- 部分型を忘れた同じ点の非零性を、測定APIの点型として固定する。 -/
theorem twoPoint_val_ne_zero : (twoPoint.val : Points E) ≠ 0 :=
  FreyWeilGeometryTest.shiftPoint_ne_zero

/-- 既存の実際の2倍原像は、零点ではあり得ない。 -/
theorem fourPoint_ne_zero : fourPoint ≠ 0 := by
  intro h
  apply fourPoint_not_two_torsion
  rw [h, smul_zero]

/-- 選択済みの分子を同じ関数体に入れたもの。 -/
noncomputable def numerator (n : ℕ) (hn : n ≠ 0) (T : Points E) (hT : n • T = 0) : (sample.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField :=
  algebraMap (sample.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).CoordinateRing (sample.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField (weilNumerator E n hn T hT)

/-- 測定する分子が非零であることを、元の構成から供給する。 -/
theorem numerator_ne_zero (n : ℕ) (hn : n ≠ 0) (T : Points E) (hT : n • T = 0) :
    numerator n hn T hT ≠ 0 := algebraMap_weilNumerator_ne_zero E n hn T hT

/-- Rは非零目標のファイバー上にあり、分子の乗法的付値はexp(−1)。 -/
theorem actual_simple_zero_value :
    finitePointValuation E fourPoint fourPoint_ne_zero
      (numerator 2 (by decide) twoPoint.val target_two_killed) = exp (-1 : ℤ) := by
  change finitePointValuation E fourPoint fourPoint_ne_zero (algebraMap (sample.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).CoordinateRing (sample.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField _) = _
  rw [valuation_weilNumerator E 2 (by decide) twoPoint.val target_two_killed]
  simp only [fourPoint_double, ite_true]

/-- 同じ零点の整数位数は+1である。付値の指数−1と区別する。 -/
theorem actual_simple_zero_order :
    finitePointOrder E fourPoint fourPoint_ne_zero
      (numerator 2 (by decide) twoPoint.val target_two_killed)
      (numerator_ne_zero 2 (by decide) twoPoint.val target_two_killed) = 1 := by
  rw [finitePointOrder, actual_simple_zero_value, log_exp, neg_neg]

/-- 同じRで零ファイバーの分母は消えない。 -/
theorem denominator_off_zero_fiber :
    finitePointOrder E fourPoint fourPoint_ne_zero
      (numerator 2 (by decide) 0 (smul_zero _))
      (numerator_ne_zero 2 (by decide) 0 (smul_zero _)) = 0 := by
  change finitePointOrder E fourPoint fourPoint_ne_zero (algebraMap (sample.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).CoordinateRing (sample.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField _) _ = _
  rw [order_weilNumerator E 2 (by decide) 0 (smul_zero _) fourPoint fourPoint_ne_zero]
  simp only [fourPoint_not_two_torsion, ite_false]

/-- 商もRでは一重零点を持つ。前章の同じSource入口を使う。 -/
theorem actual_function_simple_zero :
    finitePointOrder E fourPoint fourPoint_ne_zero
      (sample.curve_weilFunction 2 (by decide) twoPoint.val target_two_killed)
      (sample.curve_weilFunction_ne_zero 2 (by decide) twoPoint.val target_two_killed) = 1 := by
  rw [sample.curve_weilFunction_order]
  simp only [fourPoint_double, ite_true]
  split_ifs with hz
  · exact (fourPoint_not_two_torsion hz).elim
  · rfl

/-- T自体は零ファイバーに属し、分母の零点の位数は1である。 -/
theorem denominator_simple_zero :
    finitePointOrder E twoPoint.val twoPoint_val_ne_zero
      (numerator 2 (by decide) 0 (smul_zero _))
      (numerator_ne_zero 2 (by decide) 0 (smul_zero _)) = 1 := by
  change finitePointOrder E twoPoint.val _ (algebraMap (sample.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).CoordinateRing (sample.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField _) _ = _
  rw [order_weilNumerator E 2 (by decide) 0 (smul_zero _) twoPoint.val
    twoPoint_val_ne_zero]
  simp only [target_two_killed, ite_true]

/-- 非零目標Tの分子は、同じTでは消えない。2T=0≠Tだからである。 -/
theorem numerator_off_target_fiber :
    finitePointOrder E twoPoint.val twoPoint_val_ne_zero
      (numerator 2 (by decide) twoPoint.val target_two_killed)
      (numerator_ne_zero 2 (by decide) twoPoint.val target_two_killed) = 0 := by
  change finitePointOrder E twoPoint.val _ (algebraMap (sample.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).CoordinateRing (sample.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField _) _ = _
  rw [order_weilNumerator E 2 (by decide) twoPoint.val target_two_killed twoPoint.val
    twoPoint_val_ne_zero]
  simp only [target_two_killed, Ne.symm twoPoint_val_ne_zero, ite_false]

/-- 従って商の位数は−1。一重極の符号を実際の点で検査する。 -/
theorem actual_function_simple_pole :
    finitePointOrder E twoPoint.val twoPoint_val_ne_zero
      (sample.curve_weilFunction 2 (by decide) twoPoint.val target_two_killed)
      (sample.curve_weilFunction_ne_zero 2 (by decide) twoPoint.val target_two_killed) = -1 := by
  rw [sample.curve_weilFunction_order]
  simp only [target_two_killed, Ne.symm twoPoint_val_ne_zero, ite_false,
    ite_true, zero_sub]

/-- もう一段持ち上げた実際の点。両ファイバーの外の測定点を得る。 -/
noncomputable def liftPoint : Points E := (multiplication_surjective E 2 (by decide) fourPoint).choose

/-- 選んだ点の二倍はRである。 -/
theorem liftPoint_double : 2 • liftPoint = fourPoint :=
  (multiplication_surjective E 2 (by decide) fourPoint).choose_spec

/-- その測定点は無限遠点ではない。 -/
theorem liftPoint_ne_zero : liftPoint ≠ 0 := by
  intro h
  apply fourPoint_ne_zero
  rw [← liftPoint_double, h, smul_zero]

/-- RはT自身ではない。Rの二倍が非零であることから区別する。 -/
theorem fourPoint_ne_target : fourPoint ≠ twoPoint.val := by
  intro h
  apply fourPoint_not_two_torsion
  rw [h, target_two_killed]

/-- 両ファイバーの外では、商の有限点位数は零になる。 -/
theorem actual_function_off_both :
    finitePointOrder E liftPoint liftPoint_ne_zero
      (sample.curve_weilFunction 2 (by decide) twoPoint.val target_two_killed)
      (sample.curve_weilFunction_ne_zero 2 (by decide) twoPoint.val target_two_killed) = 0 := by
  rw [sample.curve_weilFunction_order]
  simp only [liftPoint_double, fourPoint_ne_target, fourPoint_ne_zero, ite_false, sub_self]

/-- 目標Oなら、同じ有限点の零点が分子・分母で相殺される。 -/
theorem zero_target_cancels :
    finitePointOrder E twoPoint.val twoPoint_val_ne_zero
      (weilFunction E 2 (by decide) 0 (smul_zero _)) (weilFunction_ne_zero E 2 (by decide) 0 (smul_zero _)) = 0 := by
  rw [order_weilFunction E 2 (by decide) 0 (smul_zero _) twoPoint.val
    twoPoint_val_ne_zero, sub_self]

/-- 指数1の境界でも、零点目標の商の位数は0。 -/
theorem one_zero_target_order :
    finitePointOrder E twoPoint.val twoPoint_val_ne_zero
      (weilFunction E 1 (by decide) 0 (smul_zero _)) (weilFunction_ne_zero E 1 (by decide) 0 (smul_zero _)) = 0 := by
  rw [order_weilFunction E 1 (by decide) 0 (smul_zero _) twoPoint.val
    twoPoint_val_ne_zero, sub_self]

/-- 37倍の零点目標についても、同じ有限点での商の位数は0。大きい多項式の展開は不要。 -/
theorem thirtySeven_zero_target_order :
    finitePointOrder E fourPoint fourPoint_ne_zero
      (weilFunction E 37 (by decide) 0 (smul_zero _)) (weilFunction_ne_zero E 37 (by decide) 0 (smul_zero _)) = 0 := by
  rw [order_weilFunction E 37 (by decide) 0 (smul_zero _) fourPoint fourPoint_ne_zero, sub_self]

/-- 非標準的な生成元を変更しても、同じ積を生成する限り実際の有限点付値は一致する。 -/
theorem arbitrary_generator_same_local_value
    (r : (sample.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).CoordinateRing)
    (hr : Ideal.span {r} = fiberIdeal E 2 (by decide) twoPoint.val) :
    letI := geometricCoordinateRing_isDedekindDomain E
    (DkMath.Lib.NumberTheory.EllipticFunctionField.placeOf E (AlgebraicClosure ℚ)
      fourPoint fourPoint_ne_zero).intValuation r =
    (DkMath.Lib.NumberTheory.EllipticFunctionField.placeOf E (AlgebraicClosure ℚ)
      fourPoint fourPoint_ne_zero).intValuation (weilNumerator E 2 (by decide) twoPoint.val target_two_killed) := by
  have := geometricCoordinateRing_isDedekindDomain E
  exact DkMath.Lib.NumberTheory.EllipticPointIdealValuation.intValuation_generator_independent
    E (AlgebraicClosure ℚ) (fiber_finite E 2 (by decide) twoPoint.val).toFinset
    hr (span_weilNumerator E 2 (by decide) twoPoint.val target_two_killed) fourPoint fourPoint_ne_zero

end FreyWeilValuationTest
