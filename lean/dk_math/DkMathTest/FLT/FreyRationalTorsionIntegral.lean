/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyRationalTorsionIntegral
import DkMathTest.FLT.FreyResidualRepresentation

#print "file: DkMathTest.FLT.FreyRationalTorsionIntegral"

/-!
# NOTE-030-001〜003の回帰: 零・打ち消し・有限性・実際の点

零を含む下界を、非零の正確な付値と区別する。
有限性を外した無限降下、p=2での非零な負付値点、p=3での単元x座標を持つ点も検査し、
今回の非負下界が後続の正の下界や有理torsion排除とは異なることを確認する。
Frey係数は既存の実在Source 2を使い、Source 37の反例の存在には依存しない。
-/
namespace FreyRationalTorsionIntegralTest
open DkMath.Lib.NumberTheory RationalTwoAdicBounds
open DkMath.Lib.Algebra.FiniteOrbitMinimum
open DkMath.FLT.Frey FreyResidualRepresentationTest
open WeierstrassCurve WeierstrassCurve.Affine

/-- 零は任意の深さの下界を満たすが、深さ0のExactではない。 -/
theorem zero_boundary : Lower 100 0 ∧ ¬ Exact 0 0 :=
  ⟨Lower.zero _, fun h => h.1 rfl⟩

/-- 零の生の付値は0である。従って付値0という等式だけでは単元性を表さない。 -/
theorem raw_zero_valuation : padicValRat 2 0 = 0 ∧ ¬ Exact 0 0 :=
  ⟨padicValRat.zero, zero_boundary.2⟩

/-- 零の0乗も1となり、下界は0である。下界の冪でこの境界を落とさない。 -/
theorem zero_power_zero : Lower 0 ((0 : ℚ) ^ 0) := by
  simpa only [Nat.cast_zero, zero_mul] using (Lower.zero 37).pow 0

/-- 異なる深さを足す場合は低い付値が正確に残る。 -/
theorem distinct_depth_sum : Exact 0 ((2 : ℚ) + 3) := by
  simpa only [min_eq_right (by decide : (0 : ℤ) ≤ 1)] using
    exact_two.add_exact_of_ne exact_three (by decide)

/-- 同じ深さではminと等しいとは限らない。3+5は深さ3に上がる。 -/
theorem equal_depth_cancellation : Exact 0 (3 : ℚ) ∧ Exact 0 (5 : ℚ) ∧ Exact 3 ((3 : ℚ) + 5) := by
  refine ⟨exact_three, ⟨by norm_num, ?_⟩, ⟨by norm_num, ?_⟩⟩
  · rw [show (5 : ℚ) = ((5 : ℕ) : ℚ) by norm_num, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 5)]
    rfl
  · rw [show (3 : ℚ) + 5 = 2 ^ 3 by norm_num, padicValRat.pow, valuation_two]
    norm_num

/-- 単元同士でも差が零になり得るため、和差の結論はLowerでなければならない。 -/
theorem unit_difference_zero : Lower 1 ((3 : ℚ) - 3) ∧ ¬ Exact 1 ((3 : ℚ) - 3) :=
  ⟨lower_one_sub_of_units exact_three exact_three, by norm_num [Exact]⟩

/-- 37乗は段階的に展開せず、冪の付値公式で処理できる。 -/
theorem power_thirtySeven : Exact 37 ((2 : ℚ) ^ 37) := by
  simpa using exact_two.pow 37

/-- 有理数の非整な値も正確な付値として扱う。 -/
theorem fractional_depth : Exact (-2) ((3 : ℚ) / 4) := by
  simpa only [show (0 - 2 : ℤ) = -2 by decide] using exact_three.div exact_four

/-- 有限性は不可欠。整数全体では負の値をさらに下げる写像が存在する。 -/
theorem infinite_drop : (∀ z : ℤ, z < 0 → z - 1 < z) ∧ ∃ z : ℤ, z < 0 := by
  constructor
  · intro z _; omega
  · exact ⟨-1, by decide⟩

/-- 実在するSource 2のa₂の整性は、向き付け条件なしで利用できる。 -/
theorem actual_source_coefficient : Lower 0 sample.rationalCurve.a₂ := sample.a₂_twoAdic_integral

/-- 同じ実在曲線ではa₂=−2。別モデルへ差し替えた整性ではない。 -/
theorem actual_source_a₂ : sample.rationalCurve.a₂ = -2 := by
  norm_num [Source.rationalCurve, sample, FreyGapCubic.normalized]

/-- 元のbが奇数の実在Sourceでも整数モデルからのa₂の証明は有効である。 -/
theorem actual_source_b_odd : ¬ Even sample.b := by decide

/-- b偶数の係数bridgeを実在する入力で試すための指数1のSource。
p≥5の反例とは区別し、γの正値性には指数条件が必要であることも検査する。 -/
def evenSource : Source 1 where
  a := -1
  b := 16
  c := 15
  a_ne := by decide
  b_ne := by decide
  c_ne := by decide
  coprime := ⟨-1, 0, by norm_num⟩
  equation := by norm_num
  normalization := ⟨by norm_num, by norm_num⟩

/-- 同じ実在Sourceではγ=0かつa₄は単元。係数の正確な評価にp≥5は不要である。 -/
theorem actual_even_coefficient : evenSource.twoAdicGamma = 0 ∧
    Exact 0 evenSource.rationalCurve.a₄ := by
  have hv : (padicValInt 2 (16 : ℤ) : ℤ) = 4 := by
    rw [← padicValRat.of_int]
    exact exact_sixteen.2
  have hγ : evenSource.twoAdicGamma = 0 := by
    change 1 * (padicValInt 2 (16 : ℤ) : ℤ) - 4 = 0
    rw [hv]
    norm_num
  refine ⟨hγ, ?_⟩
  have h := evenSource.a₄_twoAdic_exact (by decide)
  rwa [hγ] at h

/-- 指数37の係数定理は、bの偶数性を公開仮定に残す。反例の存在は主張しない。 -/
theorem source_thirtySeven_coefficients (S : Source 37) (hbe : Even S.b) :
    Exact S.twoAdicGamma S.rationalCurve.a₄ ∧ 1 ≤ S.twoAdicGamma :=
  ⟨S.a₄_twoAdic_exact hbe, S.one_le_twoAdicGamma (by decide) hbe⟩

/-- 指数37でp倍零・非零の同じ有理点から、全倍点の非負付値へ接続する。 -/
theorem source_thirtySeven_integral (S : Source 37) (hbe : Even S.b)
    (Q : S.rationalCurve.toAffine.Point) (hQp : 37 • Q = 0) (hQ0 : Q ≠ 0) (k : ℕ) :
    0 ≤ padicValRat 2 (k • Q).xc :=
  S.x_nonnegative_of_prime_torsion (by decide) (by decide) hbe Q hQp hQ0 k

/-- 2-torsionで負のx付値を持つ例の曲線。係数の下界は一般定理のものを満たす。 -/
def twoCurve : Affine ℚ := ⟨1, 8, 0, 2, 0⟩

/-- P=(−1/4,1/8)は同じ曲線の非特異な有限点である。 -/
theorem twoCurve_nonsingular : twoCurve.Nonsingular (-1 / 4) (1 / 8) := by
  norm_num [nonsingular_iff', equation_iff', twoCurve]

/-- 実際の有理点を構成する。 -/
def negativeTwoPoint : twoCurve.Point := Point.some _ _ twoCurve_nonsingular

/-- p=2を一般の非負付値定理に含めることはできない。 -/
theorem negative_two_torsion : negativeTwoPoint ≠ 0 ∧ 2 • negativeTwoPoint = 0 ∧
    padicValRat 2 negativeTwoPoint.xc = -2 := by
  refine ⟨Point.some_ne_zero _, ?_, ?_⟩
  · rw [two_nsmul]
    apply Point.add_self_of_Y_eq
    norm_num [negY, twoCurve]
  · change padicValRat 2 (-1 / 4 : ℚ) = -2
    have h : Exact 0 (1 : ℚ) := ⟨one_ne_zero, padicValRat.one⟩
    simpa using (h.neg.div exact_four).2

/-- p=2の反例の係数も、a₂が整でa₄が深さ1という条件を満たす。 -/
theorem twoCurve_coefficients : Lower 0 twoCurve.a₂ ∧ Lower 1 twoCurve.a₄ := by
  exact ⟨lower_int 8, lower_two⟩

/-- 単元x座標を持つ実際の3-torsionを作る別の曲線。 -/
def threeCurve : Affine ℚ := ⟨1, 3, 0, -2, 0⟩

/-- Q=(1,1)の非特異性。 -/
theorem threeCurve_nonsingular : threeCurve.Nonsingular 1 1 := by
  norm_num [nonsingular_iff', equation_iff', threeCurve]

/-- 実際の有理3-torsion候補。 -/
def unitThreePoint : threeCurve.Point := Point.some _ _ threeCurve_nonsingular

/-- 倍点は負の点になる。実際の接線・倍点公式で確認する。 -/
theorem unitThreePoint_double : 2 • unitThreePoint = -unitThreePoint := by
  dsimp only [unitThreePoint]
  rw [two_nsmul]
  have hy : (1 : ℚ) ≠ threeCurve.negY 1 1 := by norm_num [negY, threeCurve]
  rw [Point.add_self_of_Y_ne hy, Point.neg_some]
  simp only [Point.some.injEq]
  norm_num [addX, addY, slope_of_Y_ne rfl hy, negY, threeCurve]

/-- 位数3の実在例は非負下界を満たすが、x付値は正ではない。 -/
theorem unit_three_torsion : addOrderOf unitThreePoint = 3 ∧
    padicValRat 2 unitThreePoint.xc = 0 := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  refine ⟨addOrderOf_eq_prime ?_ (Point.some_ne_zero _), ?_⟩
  · rw [show (3 : ℕ) = 2 + 1 by decide, add_nsmul, unitThreePoint_double, one_nsmul, neg_add_cancel]
  · exact padicValRat.one

/-- 一般の有限軌道定理を実在する3-torsionの全倍点に適用する。 -/
theorem actual_three_orbit (k : ℕ) : 0 ≤ padicValRat 2 (k • unitThreePoint).xc :=
  WeierstrassTorsionValuation.x_nonnegative_of_prime_order rfl rfl rfl (lower_int 3)
    lower_two.neg unitThreePoint 3 (by decide) (by decide) unit_three_torsion.1 k

/-- 同じ3-torsion軌道の非自明な倍点では、実際のx座標も非零である。 -/
theorem actual_three_nonzero (k : ℕ) (hk : ¬ 3 ∣ k) : (k • unitThreePoint).xc ≠ 0 :=
  WeierstrassTorsionValuation.nsmul_x_nonzero_of_prime_order rfl rfl rfl unitThreePoint 3
    (by decide) (by decide) unit_three_torsion.1 k hk

end FreyRationalTorsionIntegralTest
