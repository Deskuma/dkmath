/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyRationalTorsion
import DkMathTest.FLT.FreyRationalTorsionIdentities

#print "file: DkMathTest.FLT.FreyRationalTorsion"

/-!
# NOTE-030-007: 実在する軌道、約分の境界、有理torsion排除の回帰

位数5の同じ点で七条件を実際に満たすことを示す。
γ=5は5v−4と書けず法10の5を約分できないため、この点を誤って排除しない。
一方、γ=1=5·1−4を持つ具体的な別モデルでは5倍零点が零であることを適用できる。
非零2-torsionは残り、零点や全torsionを混同しない。
-/
namespace FreyRationalTorsionTest
open DkMath.Lib.NumberTheory RationalTwoAdicBounds WeierstrassValuationOrbit
open WeierstrassCurve WeierstrassCurve.Affine
open FreyRationalTorsionPositiveTest FreyRationalTorsionBoundsTest FreyRationalTorsionIdentitiesTest

/-- 深さが一致して打ち消しが起きても、非零な差には一致時の下界を安全に使える。 -/
theorem equal_depth_nonzero_difference :
    (0 : ℤ) ≤ padicValRat 2 ((3 : ℚ) - 5) ∧ Exact 1 ((3 : ℚ) - 5) := by
  have h5 : Exact 0 (5 : ℚ) := by
    refine ⟨by norm_num, ?_⟩
    change padicValRat 2 ((5 : ℕ) : ℚ) = 0
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 5)]
    rfl
  exact ⟨(exact_three.sub_valuation_spec h5 (by norm_num)).2 rfl,
    by convert exact_two.neg using 1; norm_num⟩

/-- 差が零ならLowerは成立しても、生のpadicValRatの数値下界へは移せない。 -/
theorem zero_difference_guard : Lower 2 ((4 : ℚ) - 4) ∧
    ¬ (2 : ℤ) ≤ padicValRat 2 ((4 : ℚ) - 4) := by
  refine ⟨exact_four.lower.sub exact_four.lower, ?_⟩
  norm_num

/-- 既存の実在する位数5の点は、整数核の七条件を全て満たす。
γの素数シフト表示をまだ仮定していないので、矛盾ではない。 -/
theorem actual_five_orbit_conditions : OrbitConditions fivePoint 5 5 :=
  orbit_conditions rfl rfl rfl fiveCurve_coefficients.1 fiveCurve_a₄_exact (by decide)
    fivePoint 5 (by decide) (by decide) fivePoint_order

/-- 新しい列の定義が、前章で計算した同じ座標・分子の付値へ一致する。 -/
theorem actual_five_sequence_values :
    xValuation fivePoint 1 = 2 ∧ xValuation fivePoint 2 = 4 ∧
    squareGapValuation fivePoint = 4 ∧ productGapValuation fivePoint 2 = 5 ∧
    differenceValuation fivePoint 2 = 2 := by
  refine ⟨exact_four.2, ?_, actual_double_numerator_depth.2, actual_secant_numerator_depth.2, ?_⟩
  · simpa only [xValuation, fivePoint_double] using (show padicValRat 2 fiveDouble.xc = 4 from exact_sixteen.2)
  · unfold differenceValuation
    rw [fivePoint_double]
    have h := exact_three.mul exact_four
    norm_num only [fiveDouble, fivePoint, Point.xc_some] at h ⊢
    exact h.2

/-- 周期端点は、同じ点の群法から(p−1)Q=−Qとして証明できる。 -/
theorem actual_five_endpoint : xValuation fivePoint 4 = xValuation fivePoint 1 :=
  xValuation_endpoint fivePoint 5 (by decide) (fivePoint_order ▸ addOrderOf_nsmul_eq_zero fivePoint)

/-- γ=5のモデルには、p=5で必要な表示γ=pv−4が存在しない。 -/
theorem five_shifted_shape_fails : ¬ ∃ v : ℤ, (5 : ℤ) = 5 * v - 4 := by omega

/-- 法2γ=10では5を約分できない。整数核の約分条件を削除できないことの具体例。 -/
theorem five_modulus_cancellation_fails : (2 * 5 : ℤ) ∣ 5 * 2 ∧ ¬ (2 * 5 : ℤ) ∣ 2 := by
  norm_num

/-- γ=1=5·1−4という算術を持つ具体的モデル。これはFrey Sourceではない。 -/
def shiftedCurve : Affine ℚ := ⟨1, 0, 0, 2, 0⟩

/-- 具体的なシフト係数の曲線にも、実際の非零2-torsionは存在する。 -/
theorem shifted_curve_has_two_torsion :
    ∃ T : shiftedCurve.Point, T ≠ 0 ∧ 2 • T = 0 := by
  refine ⟨WeierstrassXReflection.twoTorsionPoint rfl (by norm_num [shiftedCurve]), ?_, ?_⟩
  · exact WeierstrassXReflection.twoTorsionPoint_ne_zero rfl _
  · exact WeierstrassXReflection.two_nsmul_twoTorsionPoint rfl rfl _

/-- 同じ具体的モデルの5倍零点は零となる。2-torsionの存在とは両立する。 -/
theorem shifted_curve_five_torsion (Q : shiftedCurve.Point) (hQ : 5 • Q = 0) : Q = 0 :=
  prime_torsion_eq_zero rfl rfl rfl (Lower.zero 0) exact_two (by decide)
    5 (by decide) (by decide) 1 (by decide) Q hQ

/-- 有理torsion排除は零点を含む等式であり、零点自体の存在を排除しない。 -/
theorem shifted_curve_zero_point : (0 : shiftedCurve.Point) = 0 :=
  shifted_curve_five_torsion 0 (nsmul_zero 5)

/-- 指数37の同じSourceで、p倍零だけからQ=0を得る。非零性providerは要求しない。 -/
theorem source_thirtySeven_torsion (S : DkMath.FLT.Frey.Source 37) (hbe : Even S.b)
    (Q : S.rationalCurve.toAffine.Point) (hQp : 37 • Q = 0) : Q = 0 :=
  S.rational_p_torsion_eq_zero (by decide) (by decide) hbe Q hQp

/-- Source 37の公開同値入口。Sourceや非零有理37-torsionの存在を主張しない。 -/
theorem source_thirtySeven_iff (S : DkMath.FLT.Frey.Source 37) (hbe : Even S.b)
    (Q : S.rationalCurve.toAffine.Point) : 37 • Q = 0 ↔ Q = 0 :=
  S.rational_p_torsion_iff (by decide) (by decide) hbe Q

end FreyRationalTorsionTest
