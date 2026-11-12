/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/



import DkMath.FLT.FreyRationalTorsionIdentities
import DkMathTest.FLT.FreyRationalTorsionBounds

#print "file: DkMathTest.FLT.FreyRationalTorsionIdentities"

/-!
# NOTE-030-006: 実際の倍点・和差と非零ガードの回帰

既存の位数5の点で分母付値・倍点等式・全内部添字の和差等式を検査する。
別の実在する位数4の点では分母は非零でも倍点のxと分子が零となる。
この境界例は、分母非零だけで分子非零を主張しない理由を示す。
-/
namespace FreyRationalTorsionIdentitiesTest
open DkMath.Lib.NumberTheory RationalTwoAdicBounds
open WeierstrassXIdentities WeierstrassTorsionIdentities
open WeierstrassCurve WeierstrassCurve.Affine
open FreyRationalTorsionPositiveTest FreyRationalTorsionBoundsTest

/-- 和差の多項式核は有理数の除算を使わず、整数上でも適用できる。 -/
theorem integer_polynomial_example :
    (((-20 : ℤ) - 16) ^ 2 + (-20 - 16) * (4 - 16) - (-24 + 4 + 16) * (4 - 16) ^ 2) *
      ((-20 + 16 + 16) ^ 2 + (-20 + 16 + 16) * (4 - 16) - (-24 + 4 + 16) * (4 - 16) ^ 2) =
      (4 * 16 - 160) ^ 2 * (4 - 16) ^ 2 :=
  plus_minus_polynomial_identity (4 : ℤ) (-20) 16 16 (-24) 160 (by norm_num) (by norm_num)

/-- Q=(4,−20)の接線分母−36は非零で深さ2。区間から正確な付値を供給できる。 -/
theorem actual_tangent_depth : Exact 2 (fivePoint.xc + 2 * fivePoint.yc) :=
  tangent_denominator_exact rfl rfl rfl fiveCurve_coefficients.1 fiveCurve_a₄_exact
    fiveCurve_nonsingular exact_four (by decide) (by decide)

/-- 同じQのx²−a₄=−144は非零で、倍点付値等式を実際の座標に適用できる。 -/
theorem actual_double_identity : fivePoint.xc ^ 2 - fiveCurve.a₄ ≠ 0 ∧
    padicValRat 2 (2 • fivePoint).xc + 2 * padicValRat 2 fivePoint.xc =
      2 * padicValRat 2 (fivePoint.xc ^ 2 - fiveCurve.a₄) :=
  double_x_valuation_of_prime_order rfl rfl rfl fiveCurve_coefficients.1
    fiveCurve_a₄_exact (by decide) fivePoint 5 (by decide) (by decide) fivePoint_order

/-- x²−a₄=−144=−3²·16の付値は4で、倍点等式4+2·2=2·4と整合する。 -/
theorem actual_double_numerator_depth : Exact 4 (fivePoint.xc ^ 2 - fiveCurve.a₄) := by
  have h := ((exact_three.pow 2).mul exact_sixteen).neg
  norm_num only [fivePoint, fiveCurve, Point.xc_some] at h ⊢
  convert h using 1

/-- 位数5の全内部添字k=2,3について、和差のガードと実際の付値漸化式を得る。 -/
theorem actual_five_interior (k : ℕ) (hk2 : 2 ≤ k) (hk3 : k ≤ 3) :
    (k • fivePoint).xc ≠ fivePoint.xc ∧
    (k • fivePoint).xc * fivePoint.xc - fiveCurve.a₄ ≠ 0 ∧
    padicValRat 2 ((k + 1) • fivePoint).xc + padicValRat 2 ((k - 1) • fivePoint).xc +
      2 * padicValRat 2 ((k • fivePoint).xc - fivePoint.xc) =
      2 * padicValRat 2 ((k • fivePoint).xc * fivePoint.xc - fiveCurve.a₄) :=
  plus_minus_x_valuation_of_prime_order rfl rfl rfl fivePoint 5 (by decide) (by decide)
    fivePoint_order k hk2 hk3

/-- k=2の分子16·4−160=−96は深さ5。和差等式の右辺は10となる。 -/
theorem actual_secant_numerator_depth :
    Exact 5 ((2 • fivePoint).xc * fivePoint.xc - fiveCurve.a₄) := by
  rw [fivePoint_double]
  have h := ((exact_three.mul exact_two).mul exact_sixteen).neg
  norm_num only [fivePoint, fiveDouble, fiveCurve, Point.xc_some] at h ⊢
  convert h using 1

/-- 内部範囲を外してk=p−1へ延ばすと、−QのxはQと一致して分母が零となる。 -/
theorem endpoint_x_coincides : (4 • fivePoint).xc = fivePoint.xc := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, mul_nsmul, fivePoint_double, fiveDouble_double]
  rfl

/-- 倍点のxが零になる境界例のモデル。有限位数p≥5という条件の必要性を検査する。 -/
def fourCurve : Affine ℚ := ⟨1, -2, 0, 1, 0⟩

/-- U=(1,0)は同じモデル上の非特異な有限点である。 -/
theorem fourCurve_nonsingular : fourCurve.Nonsingular 1 0 := by
  norm_num [nonsingular_iff', equation_iff', fourCurve]

/-- 倍点が原点Tとなる実際の有理点U。 -/
def fourPoint : fourCurve.Point := Point.some _ _ fourCurve_nonsingular

/-- 接線分母は単元でも、2U=Tなので倍点のxとx²−a₄は零となる。
従って付値恒等式の非零ガードを分母非零だけで代用してはいけない。 -/
theorem four_point_boundary : Exact 0 (fourPoint.xc + 2 * fourPoint.yc) ∧
    2 • fourPoint = WeierstrassXReflection.twoTorsionPoint (W := fourCurve) rfl (by norm_num [fourCurve]) ∧
    fourPoint.xc ^ 2 - fourCurve.a₄ = 0 := by
  refine ⟨by simpa only [fourPoint, Point.xc_some, Point.yc_some, mul_zero, add_zero]
    using (show Exact 0 (1 : ℚ) from ⟨one_ne_zero, padicValRat.one⟩), ?_, by norm_num [fourPoint, fourCurve]⟩
  dsimp only [fourPoint, WeierstrassXReflection.twoTorsionPoint]
  rw [two_nsmul]
  have hy : (0 : ℚ) ≠ fourCurve.negY 1 0 := by norm_num [fourCurve, negY]
  rw [Point.add_self_of_Y_ne hy]
  simp only [Point.some.injEq]
  norm_num [fourCurve, addX, addY, negAddY, negY, slope_of_Y_ne rfl hy]

/-- 同じUが実際に位数4であることを群法から検査する。 -/
theorem four_point_order : addOrderOf fourPoint = 4 := by
  have h2 := four_point_boundary.2.1
  have h4 : (4 : ℕ) • fourPoint = 0 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, mul_nsmul, h2]
    exact WeierstrassXReflection.two_nsmul_twoTorsionPoint rfl rfl _
  have hd : addOrderOf fourPoint ∣ 4 := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h4
  have h2ne : 2 • fourPoint ≠ 0 := by
    rw [h2]
    exact WeierstrassXReflection.twoTorsionPoint_ne_zero rfl _
  have hn2 : ¬ addOrderOf fourPoint ∣ 2 := fun h => h2ne (addOrderOf_dvd_iff_nsmul_eq_zero.mp h)
  have hpos := Nat.pos_of_dvd_of_pos hd (by decide : 0 < 4)
  have hle := Nat.le_of_dvd (by decide : 0 < 4) hd
  interval_cases addOrderOf fourPoint <;> simp_all

/-- 指数37の同じSourceから、倍点恒等式を追加providerなしで取り出す。 -/
theorem source_thirtySeven_double (S : DkMath.FLT.Frey.Source 37) (hbe : Even S.b)
    (Q : S.rationalCurve.toAffine.Point) (hQp : 37 • Q = 0) (hQ0 : Q ≠ 0) :
    Q.xc ^ 2 - S.rationalCurve.a₄ ≠ 0 ∧
    padicValRat 2 (2 • Q).xc + 2 * padicValRat 2 Q.xc =
      2 * padicValRat 2 (Q.xc ^ 2 - S.rationalCurve.a₄) :=
  S.double_x_valuation_identity (by decide) (by decide) hbe Q hQp hQ0

/-- 指数37の全2≤k≤35で和差の漸化式を供給する。ここにはb偶数の仮定は不要。 -/
theorem source_thirtySeven_interior (S : DkMath.FLT.Frey.Source 37)
    (Q : S.rationalCurve.toAffine.Point) (hQp : 37 • Q = 0) (hQ0 : Q ≠ 0)
    (k : ℕ) (hk2 : 2 ≤ k) (hk35 : k ≤ 35) :
    (k • Q).xc ≠ Q.xc ∧ (k • Q).xc * Q.xc - S.rationalCurve.a₄ ≠ 0 ∧
    padicValRat 2 ((k + 1) • Q).xc + padicValRat 2 ((k - 1) • Q).xc +
      2 * padicValRat 2 ((k • Q).xc - Q.xc) =
      2 * padicValRat 2 ((k • Q).xc * Q.xc - S.rationalCurve.a₄) :=
  S.plus_minus_x_valuation_identity (by decide) (by decide) Q hQp hQ0 k hk2 hk35

end FreyRationalTorsionIdentitiesTest
