/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyRationalTorsionPositive
import DkMathTest.FLT.FreyRationalTorsionIntegral

#print "file: DkMathTest.FLT.FreyRationalTorsionPositive"

/-!
# NOTE-030-004: 単元例外・負の三倍点・実在する5-torsion

p=3の単元x座標の例は2Q=−Qとなり、異なるx座標を要求する割線計算の例外である。
別のモデルでは単元xから実際に3Qの負付値を検査する。
さらに有理5-torsionを実際に構成し、全ての非自明な倍点に正値定理を適用する。
これらの一般モデルをFrey Sourceの反例と混同しない。
-/
namespace FreyRationalTorsionPositiveTest
open DkMath.Lib.NumberTheory RationalTwoAdicBounds
open WeierstrassPositiveValuation
open WeierstrassCurve WeierstrassCurve.Affine
open FreyRationalTorsionIntegralTest

/-- p=3では実際に単元xを持つため、正値定理の指数条件は必要である。 -/
theorem three_is_boundary : addOrderOf unitThreePoint = 3 ∧
    ¬ 1 ≤ padicValRat 2 unitThreePoint.xc := by
  refine ⟨unit_three_torsion.1, ?_⟩
  rw [unit_three_torsion.2]
  decide

/-- a₂が単元の場合の局所倍点補題を、既存の実在3-torsionに適用できる。
この結果自体は位数3を排除せず、倍点のxが元と等しい例外を残す。 -/
theorem three_double_unit : Lower 0 (threeCurve.slope 1 1 1 1) ∧
    Exact 0 (threeCurve.addX 1 1 (threeCurve.slope 1 1 1 1)) := by
  have h := double_x_unit (W := threeCurve) rfl rfl exact_three lower_two.neg
    (show Exact 0 (1 : ℚ) from ⟨one_ne_zero, padicValRat.one⟩) (lower_int 1)
  exact h.2

/-- 3-torsionの倍点は同じx座標を持つので、負の三倍点の補題のガードを満たさない。 -/
theorem three_double_x_equal : (2 • unitThreePoint).xc = unitThreePoint.xc := by
  rw [unitThreePoint_double]
  rfl

/-- 単元点から負の三倍点が生じる局所計算用モデル。 -/
def secantCurve : Affine ℚ := ⟨1, 1, 0, -2, 0⟩

/-- このモデルのU=(1,0)は非特異である。 -/
theorem secantCurve_nonsingular : secantCurve.Nonsingular 1 0 := by
  norm_num [nonsingular_iff', equation_iff', secantCurve]

/-- 同じ曲線の実際の有理点U。有限位数は仮定しない。 -/
def unitPoint : secantCurve.Point := Point.some _ _ secantCurve_nonsingular

/-- 正確な倍点座標V=(9,−33)の非特異性。 -/
theorem secantDouble_nonsingular : secantCurve.Nonsingular 9 (-33) := by
  norm_num [nonsingular_iff', equation_iff', secantCurve]

/-- 接線と倍点公式で2U=(9,−33)を確認する。 -/
theorem unitPoint_double : 2 • unitPoint = Point.some 9 (-33) secantDouble_nonsingular := by
  dsimp only [unitPoint]
  rw [two_nsmul]
  have hy : (0 : ℚ) ≠ secantCurve.negY 1 0 := by norm_num [negY, secantCurve]
  rw [Point.add_self_of_Y_ne hy]
  simp only [Point.some.injEq]
  norm_num [addX, addY, slope_of_Y_ne rfl hy, negY, secantCurve]

/-- 三倍点の座標は121/64であり、前段の単元とは異なる負の付値を持つ。 -/
theorem unitPoint_triple_x : (3 • unitPoint).xc = 121 / 64 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, unitPoint_double, one_nsmul]
  dsimp only [unitPoint]
  rw [Point.add_of_X_ne (by norm_num : (9 : ℚ) ≠ 1), Point.xc_some]
  norm_num [addX, slope_of_X_ne (by norm_num : (9 : ℚ) ≠ 1), secantCurve]

/-- 局所の負付値補題は、位数の仮定なしで実際の3Uの負付値を供給する。 -/
theorem actual_triple_negative : padicValRat 2 (3 • unitPoint).xc ≤ -2 := by
  have hx : Exact 0 (1 : ℚ) := ⟨one_ne_zero, padicValRat.one⟩
  have hx₂ : Exact 0 (secantCurve.addX 1 1 (3 : ℚ)) := by
    have h9 := exact_three.pow 2
    norm_num only [secantCurve, addX] at h9 ⊢
    simpa using h9
  have h := triple_x_valuation_negative (W := secantCurve) rfl rfl (lower_int 1)
    hx (Lower.zero 0) exact_three.lower hx₂ (by norm_num [addX, secantCurve])
  rw [unitPoint_triple_x]
  convert h.2 using 1
  norm_num [addX, addY, negAddY, negY,
    slope_of_X_ne (by norm_num : (9 : ℚ) ≠ 1), secantCurve]

/-- 正値定理を実在する位数5の点で検査するモデル。 -/
def fiveCurve : Affine ℚ := ⟨1, -24, 0, 160, 0⟩

/-- Q=(4,−20)の非特異性。 -/
theorem fiveCurve_nonsingular : fiveCurve.Nonsingular 4 (-20) := by
  norm_num [nonsingular_iff', equation_iff', fiveCurve]

/-- 位数5となる実際の有理点。 -/
def fivePoint : fiveCurve.Point := Point.some _ _ fiveCurve_nonsingular

/-- 倍点R=(16,16)も同じ曲線の非特異な点である。 -/
theorem fiveDouble_nonsingular : fiveCurve.Nonsingular 16 16 := by
  norm_num [nonsingular_iff', equation_iff', fiveCurve]

/-- 同じ曲線のRを記録する。 -/
def fiveDouble : fiveCurve.Point := Point.some _ _ fiveDouble_nonsingular

/-- Qの実際の倍点はRである。 -/
theorem fivePoint_double : 2 • fivePoint = fiveDouble := by
  dsimp only [fivePoint, fiveDouble]
  rw [two_nsmul]
  have hy : (-20 : ℚ) ≠ fiveCurve.negY 4 (-20) := by norm_num [negY, fiveCurve]
  rw [Point.add_self_of_Y_ne hy]
  simp only [Point.some.injEq]
  norm_num [addX, addY, slope_of_Y_ne rfl hy, negY, fiveCurve]

/-- Rの倍点は−Qとなる。従って4Q=−Qである。 -/
theorem fiveDouble_double : 2 • fiveDouble = -fivePoint := by
  dsimp only [fivePoint, fiveDouble]
  rw [two_nsmul]
  have hy : (16 : ℚ) ≠ fiveCurve.negY 16 16 := by norm_num [negY, fiveCurve]
  rw [Point.add_self_of_Y_ne hy, Point.neg_some]
  simp only [Point.some.injEq]
  norm_num [addX, addY, slope_of_Y_ne rfl hy, negY, fiveCurve]

/-- Qの非零性と実際の倍点計算から、位数5を証明する。 -/
theorem fivePoint_order : addOrderOf fivePoint = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply addOrderOf_eq_prime _ (Point.some_ne_zero _)
  rw [show (5 : ℕ) = 4 + 1 from rfl, add_nsmul, one_nsmul,
    show (4 : ℕ) = 2 * 2 from rfl, mul_nsmul,
    fivePoint_double, fiveDouble_double, neg_add_cancel]

/-- 位数5のモデルが一般定理の係数条件を実際に満たすことを確認する。 -/
theorem fiveCurve_coefficients : Lower 0 fiveCurve.a₂ ∧ Lower 1 fiveCurve.a₄ := by
  refine ⟨lower_int (-24), ?_⟩
  have h := lower_two.mul (lower_int 80)
  norm_num only [fiveCurve] at h ⊢
  simpa using h

/-- 実在する位数5の点の全ての非自明な倍点で正の下界を検査する。 -/
theorem actual_five_orbit_positive (k : ℕ) (hk : ¬ 5 ∣ k) :
    1 ≤ padicValRat 2 (k • fivePoint).xc :=
  nsmul_x_positive_of_prime_order rfl rfl rfl fiveCurve_coefficients.1 fiveCurve_coefficients.2
    fivePoint 5 (by decide) (by decide) fivePoint_order k hk

/-- p∤kのガードは必要。k=0の零点のxcの便宜値に正値は主張しない。 -/
theorem zero_multiple_boundary : ¬ 1 ≤ padicValRat 2 (0 • fivePoint).xc := by
  rw [zero_nsmul]
  change ¬ 1 ≤ padicValRat 2 (0 : ℚ)
  simp only [padicValRat.zero, not_le]
  decide

/-- 指数37のSourceへ、同じ有理点と明示されたb偶数条件を保って接続する。 -/
theorem source_thirtySeven_lower_bound (S : DkMath.FLT.Frey.Source 37) (hbe : Even S.b)
    (Q : S.rationalCurve.toAffine.Point) (hQp : 37 • Q = 0) (hQ0 : Q ≠ 0)
    (k : ℕ) (hk1 : 1 ≤ k) (hk36 : k ≤ 36) : 1 ≤ padicValRat 2 (k • Q).xc :=
  S.orbit_x_lower_bound (by decide) (by decide) hbe Q hQp hQ0 k hk1 hk36

end FreyRationalTorsionPositiveTest
