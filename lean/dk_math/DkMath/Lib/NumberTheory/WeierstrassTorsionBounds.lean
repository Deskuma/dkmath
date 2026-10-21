/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_FreyPackage_freyCurve_rational_p_torsion_eq_zero.lean,
frey_shallow_of_order.
Upstream blob: fe61fd5d4f94d55b5a9da38d1541903c84397df0
Modified for DkMath: reuse the independent reflection, positive lower bound and negative doubling;
preserve the original point and bound every nontrivial multiple.
-/


import DkMath.Lib.NumberTheory.WeierstrassXReflection
import DkMath.Lib.NumberTheory.WeierstrassPositiveValuation

#print "file: DkMath.Lib.NumberTheory.WeierstrassTorsionBounds"

/-!
# NOTE-030-005: 反射によって上界γ−1を得る

位数p≥5の点Qに対し、既存の下界1≤v₂(x(Q))を上界と結ぶ。
T=(0,0)、R=Q+Tとすると、反射からv₂(x(R))=γ−v₂(x(Q))である。
この値が負なら倍点でさらに下がり、0なら偶係数の方程式または単元倍点が矛盾する。
どちらの場合も2R=2Qへ戻して、元のp-torsion軌道の下界を適用する。

Rは一般にはp-torsionではない。有限位数の下界をRに直接適用しない。
ここで完成するのは各非自明な倍点の区間1≤e(k)≤γ−1であり、
整数折り返し核の倍点・和差漸化式と有理torsionの排除は後続の課題である。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassTorsionBounds
open WeierstrassCurve WeierstrassCurve.Affine
open RationalTwoAdicBounds WeierstrassXReflection
open WeierstrassNegativeValuation WeierstrassTorsionValuation WeierstrassPositiveValuation
local notation "v" => padicValRat 2
variable {W : Affine ℚ}

/-- 実際の位数p≥5の点のx付値には上界γ−1がある。
反射後の点の位数を仮定せず、その倍点が元の2Qであることだけを使う。 -/
theorem x_below_gamma_of_prime_order (h₁ : W.a₁ = 1) (h₃ : W.a₃ = 0) (h₆ : W.a₆ = 0)
    (ha₂ : Lower 0 W.a₂) {γ : ℤ} (ha₄ : Exact γ W.a₄) (hγ : 1 ≤ γ)
    (Q : W.Point) (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hQ : addOrderOf Q = p)
    {x y : ℚ} {h : W.Nonsingular x y} (hxy : Q = Point.some x y h) : v x ≤ γ - 1 := by
  have hx0 := x_nonzero_of_addOrder_eq h₁ h₃ h₆ Q p (by omega) hQ hxy
  have hxQ : Q.xc = x := by rw [hxy, Point.xc_some]
  have hxQ0 : Q.xc ≠ 0 := by rwa [hxQ]
  have ha₄L : Lower 1 W.a₄ := ha₄.lower.mono hγ
  let R := Q + twoTorsionPoint h₆ ha₄.1
  have hR0 : R ≠ 0 := add_twoTorsionPoint_ne_zero h₃ h₆ ha₄.1 Q hxQ0
  have hRns := Point.nonsingular_xc_yc hR0
  have hReq := Point.eq_some_xc_yc hR0
  have hER : Exact (γ - v x) R.xc := by
    apply exact_add_twoTorsionPoint h₃ h₆ ha₄ Q
    rw [hxQ]
    exact ⟨hx0, rfl⟩
  have h2R : 2 • R = 2 • Q := double_add_twoTorsionPoint h₃ h₆ ha₄.1 Q
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
  have h2Q0 : 2 • Q ≠ 0 := fun hz => hp2 (hQ ▸ addOrderOf_dvd_iff_nsmul_eq_zero.mpr hz)
  have hyy : R.yc ≠ W.negY R.xc R.yc := by
    intro hy
    apply h2Q0
    rw [← h2R, two_nsmul, hReq, Point.add_self_of_Y_eq hy]
  have hdouble : (2 • Q).xc = W.addX R.xc R.xc (W.slope R.xc R.xc R.yc R.yc) := by
    rw [← h2R, two_nsmul, hReq, Point.add_self_of_Y_ne hyy, Point.xc_some]
    rfl
  by_contra hlarge
  have he : γ - v x ≤ 0 := by omega
  rcases lt_or_eq_of_le he with hneg | hzero
  · obtain ⟨_, hdrop⟩ := double_x_valuation_drop h₁ h₃ h₆ ha₂ ha₄L hRns hER hneg hyy
    have hnonneg := x_nonnegative_of_prime_order h₁ h₃ h₆ ha₂ ha₄L Q p hp (by omega) hQ 2
    rw [hdouble] at hnonneg
    omega
  · rw [hzero] at hER
    have hyI := y_integral_of_x_integral h₁ h₃ h₆ ha₂ ha₄L hRns hER.lower
    by_cases hA2 : Lower 1 W.a₂
    · exact not_unit_x_of_even_a₂ h₁ h₃ h₆ hA2 ha₄L hRns hyI hER
    · have hEA2 : Exact 0 W.a₂ := by
        refine ⟨fun hz => hA2 (Or.inl hz), ?_⟩
        have hi := ha₂.le_valuation (fun hz => hA2 (Or.inl hz))
        have hn : ¬ 1 ≤ v W.a₂ := fun hh => hA2 (Or.inr hh)
        omega
      have hunit := (double_x_unit h₁ h₃ hEA2 ha₄L hER hyI).2.2
      have hpos := nsmul_x_positive_of_prime_order h₁ h₃ h₆ ha₂ ha₄L Q p hp hp5 hQ 2 hp2
      rw [hdouble, hunit.2] at hpos
      omega

/-- 正の下界と反射の上界を、同じ有限点の同じx座標についてまとめる。 -/
theorem x_bounds_of_prime_order (h₁ : W.a₁ = 1) (h₃ : W.a₃ = 0) (h₆ : W.a₆ = 0)
    (ha₂ : Lower 0 W.a₂) {γ : ℤ} (ha₄ : Exact γ W.a₄) (hγ : 1 ≤ γ)
    (Q : W.Point) (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hQ : addOrderOf Q = p)
    {x y : ℚ} {h : W.Nonsingular x y} (hxy : Q = Point.some x y h) :
    1 ≤ v x ∧ v x ≤ γ - 1 :=
  ⟨x_positive_of_prime_order h₁ h₃ h₆ ha₂ (ha₄.lower.mono hγ) Q p hp hp5 hQ hxy,
    x_below_gamma_of_prime_order h₁ h₃ h₆ ha₂ ha₄ hγ Q p hp hp5 hQ hxy⟩

/-- p∤kの倍点は位数pを保つので、軌道の同じxcにも両側の境界がある。
零倍点を含む全kへ拡張しない。 -/
theorem nsmul_x_bounds_of_prime_order (h₁ : W.a₁ = 1) (h₃ : W.a₃ = 0) (h₆ : W.a₆ = 0)
    (ha₂ : Lower 0 W.a₂) {γ : ℤ} (ha₄ : Exact γ W.a₄) (hγ : 1 ≤ γ)
    (Q : W.Point) (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hQ : addOrderOf Q = p)
    (k : ℕ) (hk : ¬ p ∣ k) : 1 ≤ v (k • Q).xc ∧ v (k • Q).xc ≤ γ - 1 := by
  have hcop : (addOrderOf Q).Coprime k := by
    rw [hQ]
    exact hp.coprime_iff_not_dvd.mpr hk
  have hord : addOrderOf (k • Q) = p := hcop.addOrderOf_nsmul.trans hQ
  have hne : k • Q ≠ 0 := fun hz => hk (hQ ▸ addOrderOf_dvd_iff_nsmul_eq_zero.mpr hz)
  exact x_bounds_of_prime_order h₁ h₃ h₆ ha₂ ha₄ hγ (k • Q) p hp hp5 hord
    (Point.eq_some_xc_yc hne)

end DkMath.Lib.NumberTheory.WeierstrassTorsionBounds
