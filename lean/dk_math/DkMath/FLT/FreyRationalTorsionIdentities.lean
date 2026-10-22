/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/



import DkMath.FLT.FreyRationalTorsionBounds
import DkMath.Lib.NumberTheory.WeierstrassTorsionIdentities

#print "file: DkMath.FLT.FreyRationalTorsionIdentities"

/-!
# NOTE-030-006: Frey Sourceの同じ点から付値恒等式へ

p倍零・非零のQから位数pを証明し、同じ座標の接線分母・倍点・和差の付値を返す。
分母の正確な深さと倍点には、前章の区間を得るためにbの偶数性を明示する。
和差恒等式には係数の付値が不要なので、b偶数の仮定を加えない。

Sourceの整数a,b,c、互いに素という情報、正規化、同じ有理曲線とQを保つ。
整数列の一括構成やtorsion排除・hratへの供給は次章の課題である。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory
open WeierstrassCurve WeierstrassCurve.Affine
variable {p : ℕ} (S : Source p)

/-- 接線分母x(Q)+2y(Q)の非零性と、x(Q)と等しい正確な深さを供給する。 -/
theorem tangent_denominator_exact_of_prime_torsion
    (hp : p.Prime) (hp5 : 5 ≤ p) (hbe : Even S.b)
    (Q : S.rationalCurve.toAffine.Point) (hQp : p • Q = 0) (hQ0 : Q ≠ 0) :
    RationalTwoAdicBounds.Exact (padicValRat 2 Q.xc) (Q.xc + 2 * Q.yc) := by
  have : Fact p.Prime := ⟨hp⟩
  exact WeierstrassTorsionIdentities.tangent_denominator_exact_of_prime_order
    S.rationalCurve_a₁ S.rationalCurve_a₃ S.rationalCurve_a₆ S.a₂_twoAdic_integral
    (S.a₄_twoAdic_exact hbe) (S.one_le_twoAdicGamma hp5 hbe)
    Q p hp hp5 (addOrderOf_eq_prime hQp hQ0) (Point.eq_some_xc_yc hQ0)

/-- 同じQから倍点分子の非零性とe(2)+2e(1)=2v₂(x(Q)²−a₄)を返す。
分母や2Qのx非零性を別のproviderに要求しない。 -/
theorem double_x_valuation_identity (hp : p.Prime) (hp5 : 5 ≤ p) (hbe : Even S.b)
    (Q : S.rationalCurve.toAffine.Point) (hQp : p • Q = 0) (hQ0 : Q ≠ 0) :
    Q.xc ^ 2 - S.rationalCurve.a₄ ≠ 0 ∧
    padicValRat 2 (2 • Q).xc + 2 * padicValRat 2 Q.xc =
      2 * padicValRat 2 (Q.xc ^ 2 - S.rationalCurve.a₄) := by
  have : Fact p.Prime := ⟨hp⟩
  exact WeierstrassTorsionIdentities.double_x_valuation_of_prime_order
    S.rationalCurve_a₁ S.rationalCurve_a₃ S.rationalCurve_a₆ S.a₂_twoAdic_integral
    (S.a₄_twoAdic_exact hbe) (S.one_le_twoAdicGamma hp5 hbe)
    Q p hp hp5 (addOrderOf_eq_prime hQp hQ0)

/-- 2≤k≤p−2で差の非零性・分子の非零性・和差の付値漸化式を供給する。
この恒等式にはbの偶数性や係数付値の入力は不要である。 -/
theorem plus_minus_x_valuation_identity (hp : p.Prime) (hp5 : 5 ≤ p)
    (Q : S.rationalCurve.toAffine.Point) (hQp : p • Q = 0) (hQ0 : Q ≠ 0)
    (k : ℕ) (hk2 : 2 ≤ k) (hkp : k ≤ p - 2) :
    (k • Q).xc ≠ Q.xc ∧ (k • Q).xc * Q.xc - S.rationalCurve.a₄ ≠ 0 ∧
    padicValRat 2 ((k + 1) • Q).xc + padicValRat 2 ((k - 1) • Q).xc +
      2 * padicValRat 2 ((k • Q).xc - Q.xc) =
      2 * padicValRat 2 ((k • Q).xc * Q.xc - S.rationalCurve.a₄) := by
  have : Fact p.Prime := ⟨hp⟩
  exact WeierstrassTorsionIdentities.plus_minus_x_valuation_of_prime_order
    S.rationalCurve_a₁ S.rationalCurve_a₃ S.rationalCurve_a₆
    Q p hp hp5 (addOrderOf_eq_prime hQp hQ0) k hk2 hkp

end DkMath.FLT.Frey.Source
