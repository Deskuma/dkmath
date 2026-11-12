/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic.LinearCombination

#print "file: DkMath.Lib.Algebra.ValuationQuadraticRoot"

/-!
# NOTE-032-003A: 二次式の整根を付値で制御する

[DkMath.Lib] モニック二次式の根の整性と、最高次係数が非単元の二次式の整根の一意性。
前者は接線方向、後者は2上の臨界中心に使う。完備性・離散性・Hensel補題は不要である。
付値は乗法的であり、「小さい」はv<1を表す。最高次係数が小さく一次係数が単元なら、
二つの整根の差に掛かる因子も単元なので、二根は一致する。
-/
namespace DkMath.Lib.Algebra.ValuationQuadraticRoot
variable {K : Type*} [Field K]

/-- [DkMath.Lib] モニック二次式の係数が整なら、その根も整である。
v(z)>1ならz²の付値がaz,bより大きくなることを、積z(z+a)=−bで確かめる。 -/
theorem mem_of_monic_quadratic (A : ValuationSubring K) {a b z : K}
    (ha : a ∈ A) (hb : b ∈ A) (hz : z ^ 2 + a * z + b = 0) : z ∈ A := by
  by_contra hn
  have hlarge : 1 < A.valuation z := lt_of_not_ge fun h => hn ((A.valuation_le_one_iff z).mp h)
  have hza : A.valuation (z + a) = A.valuation z :=
    Valuation.map_add_eq_of_lt_left _ (((A.valuation_le_one_iff a).mpr ha).trans_lt hlarge)
  have hfactor : z * (z + a) = -b := by linear_combination hz
  have hprod : 1 < A.valuation (z * (z + a)) := by
    rw [map_mul, hza]
    exact hlarge.trans (by simpa using mul_lt_mul_of_pos_left hlarge (zero_lt_one.trans hlarge))
  rw [hfactor, Valuation.map_neg] at hprod
  exact (not_lt.mpr ((A.valuation_le_one_iff b).mpr hb)) hprod

/-- [DkMath.Lib] 単元bに非単元aと整元zの積を加えても付値は1である。
整根の比較で現れるb+a(x+y)が零でないことを、付値の等号として保持する。 -/
theorem valuation_linear_eq_one (A : ValuationSubring K) {a b z : K}
    (ha : A.valuation a < 1) (hb : A.valuation b = 1) (hz : z ∈ A) :
    A.valuation (b + a * z) = 1 := by
  have hsmall : A.valuation (a * z) < 1 := by
    rw [map_mul]
    exact (mul_le_of_le_one_right' ((A.valuation_le_one_iff z).mpr hz)).trans_lt ha
  rw [Valuation.map_add_eq_of_lt_left _ (by rwa [hb]), hb]

/-- [DkMath.Lib] 最高次係数aが非単元、一次係数bが単元なら二次式の整根は高々一つ。
二つの根の方程式を引くと(x−y)(b+a(x+y))=0となり、第二因子は単元である。
根の存在はこの一意性の主張には含めない。 -/
theorem eq_of_integral_quadratic_roots (A : ValuationSubring K) {a b c x y : K}
    (ha : A.valuation a < 1) (hb : A.valuation b = 1) (hx : x ∈ A) (hy : y ∈ A)
    (hfx : a * x ^ 2 + b * x + c = 0) (hfy : a * y ^ 2 + b * y + c = 0) : x = y := by
  have hf : (x - y) * (b + a * (x + y)) = 0 := by linear_combination hfx - hfy
  have hunit := valuation_linear_eq_one A ha hb (add_mem hx hy)
  have hne : b + a * (x + y) ≠ 0 := by
    intro h
    rw [h, map_zero] at hunit
    exact zero_ne_one hunit
  exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right hne)

end DkMath.Lib.Algebra.ValuationQuadraticRoot
