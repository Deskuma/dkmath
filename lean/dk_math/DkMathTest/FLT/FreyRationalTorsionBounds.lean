/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.FLT.FreyRationalTorsionBounds
import DkMathTest.FLT.FreyRationalTorsionPositive

#print "file: DkMathTest.FLT.FreyRationalTorsionBounds"

/-!
# NOTE-030-005: 反射・位数の区別・鋭い上界の回帰

前章の実在する5-torsionを使い、反射、倍点の一致、移動後の点が5倍零でないことを検査する。
a₄=160のγは5で、2Qのx=16は上界γ−1=4に実際に達する。
これは一般のWeierstrassモデルの例であり、Frey SourceやFLTの反例を作らない。
-/
namespace FreyRationalTorsionBoundsTest
open DkMath.Lib.NumberTheory RationalTwoAdicBounds
open WeierstrassXReflection WeierstrassTorsionBounds
open WeierstrassCurve WeierstrassCurve.Affine
open FreyRationalTorsionPositiveTest

/-- 160=5·2⁵の正確な付値を、非零性も含めて証明する。 -/
theorem fiveCurve_a₄_exact : Exact 5 fiveCurve.a₄ := by
  have h5 : Exact 0 (5 : ℚ) := by
    refine ⟨by norm_num, ?_⟩
    change padicValRat 2 ((5 : ℕ) : ℚ) = 0
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 5)]
    rfl
  have hh := h5.mul (exact_two.pow 5)
  norm_num only [fiveCurve] at hh ⊢
  convert hh using 1

/-- 実例の同じ曲線上のT=(0,0)。 -/
def fiveT : fiveCurve.Point := twoTorsionPoint rfl fiveCurve_a₄_exact.1

/-- Tは非零で2倍零となる。 -/
theorem fiveT_order_two : fiveT ≠ 0 ∧ 2 • fiveT = 0 :=
  ⟨twoTorsionPoint_ne_zero rfl fiveCurve_a₄_exact.1,
    two_nsmul_twoTorsionPoint rfl rfl fiveCurve_a₄_exact.1⟩

/-- 同じQに反射を二回適用するとQに戻り、反射後の倍点も2Qとなる。 -/
theorem actual_translation_laws : (fivePoint + fiveT) + fiveT = fivePoint ∧
    2 • (fivePoint + fiveT) = 2 • fivePoint :=
  ⟨add_twoTorsionPoint_twice rfl rfl fiveCurve_a₄_exact.1 fivePoint,
    double_add_twoTorsionPoint rfl rfl fiveCurve_a₄_exact.1 fivePoint⟩

/-- x(Q)=4の反射は160/4=40となる。 -/
theorem actual_reflected_x : (fivePoint + fiveT).xc = 40 := by
  rw [show fiveT = twoTorsionPoint rfl fiveCurve_a₄_exact.1 from rfl,
    add_twoTorsionPoint_x rfl rfl fiveCurve_a₄_exact.1 fivePoint
      (by norm_num [fivePoint])]
  norm_num [fivePoint, fiveCurve]

/-- Qの深さ2がγ−2=3へ反射する。零をExactと扱わない。 -/
theorem actual_reflected_depth : Exact 3 (fivePoint + fiveT).xc := by
  exact exact_add_twoTorsionPoint rfl rfl fiveCurve_a₄_exact fivePoint exact_four

/-- 奇数倍の挙動を実際の点で確認する。移動後の点の5倍はTである。 -/
theorem actual_translated_five_multiple : 5 • (fivePoint + fiveT) = fiveT :=
  odd_nsmul_add_twoTorsionPoint rfl rfl fiveCurve_a₄_exact.1 fivePoint 5
    (by decide) (fivePoint_order ▸ addOrderOf_nsmul_eq_zero fivePoint)

/-- P+Tを5-torsionと誤認すると破綻することを検査する。 -/
theorem translated_not_five_torsion : 5 • (fivePoint + fiveT) ≠ 0 := by
  rw [actual_translated_five_multiple]
  exact fiveT_order_two.1

/-- 位数5の全非自明な倍点に、実装した区間定理を適用できる。 -/
theorem actual_five_orbit_bounds (k : ℕ) (hk : ¬ 5 ∣ k) :
    1 ≤ padicValRat 2 (k • fivePoint).xc ∧ padicValRat 2 (k • fivePoint).xc ≤ 4 :=
  nsmul_x_bounds_of_prime_order rfl rfl rfl fiveCurve_coefficients.1
    fiveCurve_a₄_exact (by decide) fivePoint 5 (by decide) (by decide) fivePoint_order k hk

/-- 2Qのx=16は深さ4であり、上界γ−1はこの一般モデルで鋭い。 -/
theorem upper_bound_attained : padicValRat 2 (2 • fivePoint).xc = 4 ∧
    ¬ padicValRat 2 (2 • fivePoint).xc ≤ 3 := by
  rw [fivePoint_double]
  have he : padicValRat 2 fiveDouble.xc = 4 := exact_sixteen.2
  rw [he]
  norm_num

/-- 原点Tでは分母x=0であり、P+Tは零点となる。
反射の分母ガードを外した座標議論に進まないための群法の境界検査。 -/
theorem origin_translation_boundary : fiveT.xc = 0 ∧ fiveT + fiveT = 0 ∧
    (0 : fiveCurve.Point) + fiveT = fiveT := by
  refine ⟨rfl, ?_, zero_add _⟩
  simpa only [two_nsmul] using fiveT_order_two.2

/-- 指数37の同じSourceと同じ点から、全1≤k≤36の区間入力を供給する。
Sourceや非零有理37-torsionの存在を主張する定理ではない。 -/
theorem source_thirtySeven_bounds (S : DkMath.FLT.Frey.Source 37) (hbe : Even S.b)
    (Q : S.rationalCurve.toAffine.Point) (hQp : 37 • Q = 0) (hQ0 : Q ≠ 0)
    (k : ℕ) (hk1 : 1 ≤ k) (hk36 : k ≤ 36) :
    1 ≤ padicValRat 2 (k • Q).xc ∧ padicValRat 2 (k • Q).xc ≤ S.twoAdicGamma - 1 :=
  S.orbit_x_bounds (by decide) (by decide) hbe Q hQp hQ0 k hk1 hk36

end FreyRationalTorsionBoundsTest
