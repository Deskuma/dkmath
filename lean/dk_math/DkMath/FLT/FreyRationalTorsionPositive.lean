/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyRationalTorsionIntegral
import DkMath.Lib.NumberTheory.WeierstrassPositiveValuation

#print "file: DkMath.FLT.FreyRationalTorsionPositive"

/-!
# NOTE-030-004: 同じFrey Sourceのx付値を非負から正へ進める

係数の2進性質と、2Q・3Qによる単元座標の排除を同じ有理曲線へ供給する。
pの素数性、p≥5、bの偶数性、同じQの非零性とp倍零を公開仮定として保持する。
全倍点に非負の下界がある前章とは異なり、正の下界にはp∤kが必要である。
特にk=0では零点のxc=0という便宜値を用いるので、その付値は0のままである。

これで整数折り返し核が要求する下界1≤e(k)は得られるが、上界γ−1や漸化式は
まだ供給していない。有理torsion排除・hrat・既約性はこの章では完成しない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory
open WeierstrassCurve WeierstrassCurve.Affine
variable {p : ℕ} (S : Source p)

/-- 位数p≥5の同じ有限点のx付値は正である。座標と非特異性の証拠を保持する。 -/
theorem x_positive_of_prime_order (hp : p.Prime) (hp5 : 5 ≤ p) (hbe : Even S.b)
    (Q : S.rationalCurve.toAffine.Point) (hQ : addOrderOf Q = p)
    {x y : ℚ} {h : S.rationalCurve.toAffine.Nonsingular x y}
    (hxy : Q = Point.some x y h) : 1 ≤ padicValRat 2 x :=
  WeierstrassPositiveValuation.x_positive_of_prime_order
    S.rationalCurve_a₁ S.rationalCurve_a₃ S.rationalCurve_a₆
    S.a₂_twoAdic_integral (S.a₄_twoAdic_positive hp5 hbe) Q p hp hp5 hQ hxy

/-- 同じ点のpで割れない倍点について正のx付値を供給する。 -/
theorem nsmul_x_positive_of_prime_order (hp : p.Prime) (hp5 : 5 ≤ p) (hbe : Even S.b)
    (Q : S.rationalCurve.toAffine.Point) (hQ : addOrderOf Q = p) (k : ℕ) (hk : ¬ p ∣ k) :
    1 ≤ padicValRat 2 (k • Q).xc :=
  WeierstrassPositiveValuation.nsmul_x_positive_of_prime_order
    S.rationalCurve_a₁ S.rationalCurve_a₃ S.rationalCurve_a₆
    S.a₂_twoAdic_integral (S.a₄_twoAdic_positive hp5 hbe) Q p hp hp5 hQ k hk

/-- p倍零・非零の点から位数pを導き、位数providerなしで正の下界を得る。 -/
theorem nsmul_x_positive_of_prime_torsion (hp : p.Prime) (hp5 : 5 ≤ p) (hbe : Even S.b)
    (Q : S.rationalCurve.toAffine.Point) (hQp : p • Q = 0) (hQ0 : Q ≠ 0)
    (k : ℕ) (hk : ¬ p ∣ k) : 1 ≤ padicValRat 2 (k • Q).xc := by
  have : Fact p.Prime := ⟨hp⟩
  exact S.nsmul_x_positive_of_prime_order hp hp5 hbe Q (addOrderOf_eq_prime hQp hQ0) k hk

/-- 整数軌道の1≤k≤p−1という添字範囲では、p∤kを実際に供給できる。
これは下界側の接続であり、上界や加法漸化式の接続ではない。 -/
theorem orbit_x_lower_bound (hp : p.Prime) (hp5 : 5 ≤ p) (hbe : Even S.b)
    (Q : S.rationalCurve.toAffine.Point) (hQp : p • Q = 0) (hQ0 : Q ≠ 0)
    (k : ℕ) (hk1 : 1 ≤ k) (hkp : k ≤ p - 1) : 1 ≤ padicValRat 2 (k • Q).xc :=
  S.nsmul_x_positive_of_prime_torsion hp hp5 hbe Q hQp hQ0 k
    (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))

end DkMath.FLT.Frey.Source
