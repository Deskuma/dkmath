/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyRationalTorsionValuation
import DkMath.Lib.NumberTheory.WeierstrassTorsionValuation

#print "file: DkMath.FLT.FreyRationalTorsionIntegral"

/-!
# NOTE-030-003: 同じ有理Frey曲線の点から非負のx付値へ

Sourceの係数について既に証明した2進整性を、一般の有限軌道の定理へ供給する。
同じS、同じQ、同じkQの座標を保ち、p≥5とbの偶数性を引数として明記する。
非零p-torsion点の位数がpであることも素数性から導き、別のproviderにしない。

得られる下界はv₂(x(kQ))≥0である。零ではない有限座標であっても付値0はまだ
排除していない。後続030-004で単元の場合を扱い、その後の上界・漸化式へ進む。
有理p-torsion排除、固定torsion排除、既約性はこのファイルの結論には含めない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory RationalTwoAdicBounds
open WeierstrassCurve WeierstrassCurve.Affine
variable {p : ℕ} (S : Source p)

/-- 位数が指数pに等しい有限点のx座標は非零。p>2だけでよい。 -/
theorem x_nonzero_of_addOrder_eq_prime (hp2 : 2 < p) (Q : S.rationalCurve.toAffine.Point)
    (hQ : addOrderOf Q = p) {x y : ℚ} {h : S.rationalCurve.toAffine.Nonsingular x y}
    (hxy : Q = Point.some x y h) : x ≠ 0 :=
  WeierstrassTorsionValuation.x_nonzero_of_addOrder_eq
    S.rationalCurve_a₁ S.rationalCurve_a₃ S.rationalCurve_a₆ Q p hp2 hQ hxy

/-- 位数pの点の全倍点で負のx付値を排除する。向き付けのb偶数条件を明示する。 -/
theorem x_nonnegative_of_prime_order (hp : p.Prime) (hp5 : 5 ≤ p) (hbe : Even S.b)
    (Q : S.rationalCurve.toAffine.Point) (hQ : addOrderOf Q = p) (k : ℕ) :
    0 ≤ padicValRat 2 (k • Q).xc :=
  WeierstrassTorsionValuation.x_nonnegative_of_prime_order
    S.rationalCurve_a₁ S.rationalCurve_a₃ S.rationalCurve_a₆
    S.a₂_twoAdic_integral (S.a₄_twoAdic_positive hp5 hbe) Q p hp (by omega) hQ k

/-- pで割れない倍点のx座標は非零。非負付値の定理とは別にこのガードを保持する。 -/
theorem nsmul_x_nonzero_of_prime_order (hp : p.Prime) (hp2 : 2 < p)
    (Q : S.rationalCurve.toAffine.Point) (hQ : addOrderOf Q = p) (k : ℕ) (hk : ¬ p ∣ k) :
    (k • Q).xc ≠ 0 :=
  WeierstrassTorsionValuation.nsmul_x_nonzero_of_prime_order
    S.rationalCurve_a₁ S.rationalCurve_a₃ S.rationalCurve_a₆ Q p hp hp2 hQ k hk

/-- p倍で零になる非零点から、位数providerなしで全倍点の非負付値を得る。
Q≠0とpの素数性を用いて位数がpであることを実際に証明する。 -/
theorem x_nonnegative_of_prime_torsion (hp : p.Prime) (hp5 : 5 ≤ p) (hbe : Even S.b)
    (Q : S.rationalCurve.toAffine.Point) (hQp : p • Q = 0) (hQ0 : Q ≠ 0) (k : ℕ) :
    0 ≤ padicValRat 2 (k • Q).xc := by
  have : Fact p.Prime := ⟨hp⟩
  exact S.x_nonnegative_of_prime_order hp hp5 hbe Q (addOrderOf_eq_prime hQp hQ0) k

end DkMath.FLT.Frey.Source
