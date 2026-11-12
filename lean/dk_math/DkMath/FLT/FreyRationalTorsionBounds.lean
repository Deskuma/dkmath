/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.FLT.FreyRationalTorsionPositive
import DkMath.Lib.NumberTheory.WeierstrassTorsionBounds

#print "file: DkMath.FLT.FreyRationalTorsionBounds"

/-!
# NOTE-030-005: 同じFrey Sourceから付値の区間を供給する

a₄の正確な付値γ=p·v₂(b)−4と1≤γを、反射による上界の一般定理へ渡す。
ここでの曲線も点も前章と同じであり、Sourceの整数座標・互いに素という情報・
正規化を変更しない。pの素数性、p≥5、bの偶数性を公開仮定として保持する。

これで整数軌道核の入力のうち1≤e(k)≤γ−1が実際のkQから得られる。
倍点・和差漸化式は未接続なので、有理torsion排除やhratの完成は主張しない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory
open WeierstrassCurve WeierstrassCurve.Affine
variable {p : ℕ} (S : Source p)

/-- 同じSourceの有理モデル上のT=(0,0)。偶数性からa₄≠0を供給する。 -/
def rationalTwoTorsionPoint (hbe : Even S.b) : S.rationalCurve.toAffine.Point :=
  WeierstrassXReflection.twoTorsionPoint S.rationalCurve_a₆ (S.a₄_twoAdic_exact hbe).1

/-- 同じ曲線上の実際の和P+Tのx座標。分母P.xc≠0を明示する。 -/
theorem x_reflection_by_two_torsion (hbe : Even S.b)
    (P : S.rationalCurve.toAffine.Point) (hx : P.xc ≠ 0) :
    (P + S.rationalTwoTorsionPoint hbe).xc = S.rationalCurve.a₄ / P.xc :=
  WeierstrassXReflection.add_twoTorsionPoint_x S.rationalCurve_a₃ S.rationalCurve_a₆
    (S.a₄_twoAdic_exact hbe).1 P hx

/-- 位数p≥5の同じ有限点のx付値の上界。向き付き条件をSourceへ暗黙に追加しない。 -/
theorem x_below_gamma_of_prime_order (hp : p.Prime) (hp5 : 5 ≤ p) (hbe : Even S.b)
    (Q : S.rationalCurve.toAffine.Point) (hQ : addOrderOf Q = p)
    {x y : ℚ} {h : S.rationalCurve.toAffine.Nonsingular x y}
    (hxy : Q = Point.some x y h) : padicValRat 2 x ≤ S.twoAdicGamma - 1 :=
  WeierstrassTorsionBounds.x_below_gamma_of_prime_order
    S.rationalCurve_a₁ S.rationalCurve_a₃ S.rationalCurve_a₆ S.a₂_twoAdic_integral
    (S.a₄_twoAdic_exact hbe) (S.one_le_twoAdicGamma hp5 hbe) Q p hp hp5 hQ hxy

/-- 位数を指定した点のpで割れない倍点に、正の下界と上界を同時に供給する。 -/
theorem nsmul_x_bounds_of_prime_order (hp : p.Prime) (hp5 : 5 ≤ p) (hbe : Even S.b)
    (Q : S.rationalCurve.toAffine.Point) (hQ : addOrderOf Q = p) (k : ℕ) (hk : ¬ p ∣ k) :
    1 ≤ padicValRat 2 (k • Q).xc ∧ padicValRat 2 (k • Q).xc ≤ S.twoAdicGamma - 1 :=
  WeierstrassTorsionBounds.nsmul_x_bounds_of_prime_order
    S.rationalCurve_a₁ S.rationalCurve_a₃ S.rationalCurve_a₆ S.a₂_twoAdic_integral
    (S.a₄_twoAdic_exact hbe) (S.one_le_twoAdicGamma hp5 hbe) Q p hp hp5 hQ k hk

/-- p倍零・非零から位数pを導き、追加の位数providerなしで軌道の区間を得る。 -/
theorem nsmul_x_bounds_of_prime_torsion (hp : p.Prime) (hp5 : 5 ≤ p) (hbe : Even S.b)
    (Q : S.rationalCurve.toAffine.Point) (hQp : p • Q = 0) (hQ0 : Q ≠ 0)
    (k : ℕ) (hk : ¬ p ∣ k) :
    1 ≤ padicValRat 2 (k • Q).xc ∧ padicValRat 2 (k • Q).xc ≤ S.twoAdicGamma - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  exact S.nsmul_x_bounds_of_prime_order hp hp5 hbe Q (addOrderOf_eq_prime hQp hQ0) k hk

/-- 整数折り返し核の添字範囲1≤k≤p−1に対し、同じkQから両側の境界を得る。
e(k)の存在を仮定せず、実際のxcの2進付値を返す。 -/
theorem orbit_x_bounds (hp : p.Prime) (hp5 : 5 ≤ p) (hbe : Even S.b)
    (Q : S.rationalCurve.toAffine.Point) (hQp : p • Q = 0) (hQ0 : Q ≠ 0)
    (k : ℕ) (hk1 : 1 ≤ k) (hkp : k ≤ p - 1) :
    1 ≤ padicValRat 2 (k • Q).xc ∧ padicValRat 2 (k • Q).xc ≤ S.twoAdicGamma - 1 :=
  S.nsmul_x_bounds_of_prime_torsion hp hp5 hbe Q hQp hQ0 k
    (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))

end DkMath.FLT.Frey.Source
