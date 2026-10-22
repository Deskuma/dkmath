/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyRationalTorsionIdentities
import DkMath.Lib.NumberTheory.WeierstrassValuationOrbit

#print "file: DkMath.FLT.FreyRationalTorsion"

/-!
# NOTE-030-007: 向き付けたFrey Sourceの有理p-torsionを排除する

同じSourceの正規化有理モデルを用い、a₂の整性とa₄の正確な付値を一般の軌道定理へ渡す。
γ=p·v₂(b)−4の表示が整数核の素数約分を可能にする。
元のa,b,c、互いに素という情報、正規化、同じ曲線とQを一切取り替えない。

公開仮定はpの素数性、p≥5、Even S.bである。任意のp倍零点Qは零となり、
非零有理p-torsionや位数・整数列のproviderは必要ない。
ガロア固定点の有理点への降下との接続は030-008、fixed/cofixedとcofixed排除は別の課題である。
この章は残余表現の無条件既約性や一般FLTを証明したものではない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory
open WeierstrassCurve WeierstrassCurve.Affine
variable {p : ℕ} (S : Source p)

/-- 同じSourceの非零p倍零点を仮定すると、実際の座標から整数核の七条件が全て得られる。
この入口は教科書として入力の構成を見せるものであり、点の存在を主張しない。 -/
theorem valuationOrbit_conditions (hp : p.Prime) (hp5 : 5 ≤ p) (hbe : Even S.b)
    (Q : S.rationalCurve.toAffine.Point) (hQp : p • Q = 0) (hQ0 : Q ≠ 0) :
    WeierstrassValuationOrbit.OrbitConditions Q p S.twoAdicGamma := by
  have : Fact p.Prime := ⟨hp⟩
  exact WeierstrassValuationOrbit.orbit_conditions S.rationalCurve_a₁ S.rationalCurve_a₃
    S.rationalCurve_a₆ S.a₂_twoAdic_integral (S.a₄_twoAdic_exact hbe)
    (S.one_le_twoAdicGamma hp5 hbe) Q p hp hp5 (addOrderOf_eq_prime hQp hQ0)

/-- 素数p≥5・b偶数という明示された条件の下で、同じ有理曲線のp倍零点は零である。
γの表示・係数・全七条件を同じSourceとQから供給し、有理torsion排除を閉じる。 -/
theorem rational_p_torsion_eq_zero (hp : p.Prime) (hp5 : 5 ≤ p) (hbe : Even S.b)
    (Q : S.rationalCurve.toAffine.Point) (hQp : p • Q = 0) : Q = 0 :=
  WeierstrassValuationOrbit.prime_torsion_eq_zero S.rationalCurve_a₁ S.rationalCurve_a₃
    S.rationalCurve_a₆ S.a₂_twoAdic_integral (S.a₄_twoAdic_exact hbe)
    (S.one_le_twoAdicGamma hp5 hbe) p hp hp5 (padicValInt 2 S.b : ℤ) rfl Q hQp

/-- 同じモデルのp倍零と零点が同値になる公開入口。逆方向は零点の群法だけである。 -/
theorem rational_p_torsion_iff (hp : p.Prime) (hp5 : 5 ≤ p) (hbe : Even S.b)
    (Q : S.rationalCurve.toAffine.Point) : p • Q = 0 ↔ Q = 0 := by
  refine ⟨S.rational_p_torsion_eq_zero hp hp5 hbe Q, ?_⟩
  intro hQ
  rw [hQ, nsmul_zero]

end DkMath.FLT.Frey.Source
