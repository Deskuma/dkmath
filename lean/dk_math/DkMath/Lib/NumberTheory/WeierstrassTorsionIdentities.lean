/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_FreyPackage_freyCurve_rational_p_torsion_eq_zero.lean,
frey_E_D and the nonzero-factor arguments preceding arith_core.
Upstream blob: fe61fd5d4f94d55b5a9da38d1541903c84397df0
Modified for DkMath: supply all local identity guards from the actual prime-order orbit;
isolate the recurrence before defining the integer-kernel input in chapter 007.
-/



import DkMath.Lib.NumberTheory.WeierstrassXIdentities

#print "file: DkMath.Lib.NumberTheory.WeierstrassTorsionIdentities"

/-!
# NOTE-030-006: 同じ素数位数の軌道が恒等式のガードを供給する

局所恒等式へ渡す非零性を仮定のまま残さず、同じQの位数pから証明する。
2≤k≤p−2ではkQ≠±Qなのでx(kQ)≠x(Q)であり、(k±1)Qのxも非零である。
前章の区間条件が接線分母の正確な付値を供給する。

ここでは実際の座標の倍点・和差の付値等式までを公開する。
e,A,B,A₁の一括定義、min条件と周期端点の整理、整数折り返し核の適用は030-007へ残す。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassTorsionIdentities
open WeierstrassCurve WeierstrassCurve.Affine
open RationalTwoAdicBounds WeierstrassTorsionValuation WeierstrassTorsionBounds
open WeierstrassXIdentities
local notation "v" => padicValRat 2
variable {W : Affine ℚ}

/-- 2≤k≤p−2の軌道内点はQと異なるx座標を持つ。
x一致ならkQ=QまたはkQ=−Qであり、位数pがk−1またはk+1を割る矛盾を得る。 -/
theorem nsmul_x_ne_x_of_prime_order (Q : W.Point) (p : ℕ) (hp5 : 5 ≤ p)
    (hQ : addOrderOf Q = p) (k : ℕ) (hk2 : 2 ≤ k) (hkp : k ≤ p - 2) :
    (k • Q).xc ≠ Q.xc := by
  have hp1 : ¬ p ∣ 1 := Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
  have hpk : ¬ p ∣ k := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hpplus : ¬ p ∣ k + 1 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hpminus : ¬ p ∣ k - 1 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hQ0 : Q ≠ 0 := by
    intro hz
    have h1 : (1 : ℕ) • Q = 0 := by rw [hz, nsmul_zero]
    exact hp1 (hQ ▸ addOrderOf_dvd_iff_nsmul_eq_zero.mpr h1)
  have hk0 : k • Q ≠ 0 := fun hz => hpk (hQ ▸ addOrderOf_dvd_iff_nsmul_eq_zero.mpr hz)
  have hQr := Point.eq_some_xc_yc hQ0
  have hkr := Point.eq_some_xc_yc hk0
  intro he
  rcases (Point.X_eq_iff (h₁ := Point.nonsingular_xc_yc hk0)
    (h₂ := Point.nonsingular_xc_yc hQ0)).mp he with he | he
  · have he' : k • Q = Q := hkr.trans (he.trans hQr.symm)
    have hh : (k - 1) • Q + Q = k • Q := by
      rw [← succ_nsmul, Nat.sub_add_cancel (by omega)]
    rw [he'] at hh
    have hz : (k - 1) • Q = 0 := by
      have hc := congrArg (· - Q) hh
      simpa using hc
    exact hpminus (hQ ▸ addOrderOf_dvd_iff_nsmul_eq_zero.mpr hz)
  · have he' : k • Q = -Q := hkr.trans (he.trans (congrArg Neg.neg hQr).symm)
    have hz : (k + 1) • Q = 0 := by rw [succ_nsmul, he', neg_add_cancel]
    exact hpplus (hQ ▸ addOrderOf_dvd_iff_nsmul_eq_zero.mpr hz)

/-- 位数p≥5の有限点では、既存の区間定理から接線分母の正確な付値を得る。 -/
theorem tangent_denominator_exact_of_prime_order
    (h₁ : W.a₁ = 1) (h₃ : W.a₃ = 0) (h₆ : W.a₆ = 0)
    (ha₂ : Lower 0 W.a₂) {γ : ℤ} (ha₄ : Exact γ W.a₄) (hγ : 1 ≤ γ)
    (Q : W.Point) (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hQ : addOrderOf Q = p)
    {x y : ℚ} {h : W.Nonsingular x y} (hxy : Q = Point.some x y h) :
    Exact (v x) (x + 2 * y) := by
  have hx := x_nonzero_of_addOrder_eq h₁ h₃ h₆ Q p (by omega) hQ hxy
  obtain ⟨hlo, hhi⟩ := x_bounds_of_prime_order h₁ h₃ h₆ ha₂ ha₄ hγ Q p hp hp5 hQ hxy
  exact tangent_denominator_exact h₁ h₃ h₆ ha₂ ha₄ h ⟨hx, rfl⟩ hlo hhi

/-- 同じ位数pのQについて、倍点分子の非零性と付値等式を仮定なしで供給する。
2Qのx非零性と接線分母のExactを実際の軌道から証明する。 -/
theorem double_x_valuation_of_prime_order
    (h₁ : W.a₁ = 1) (h₃ : W.a₃ = 0) (h₆ : W.a₆ = 0)
    (ha₂ : Lower 0 W.a₂) {γ : ℤ} (ha₄ : Exact γ W.a₄) (hγ : 1 ≤ γ)
    (Q : W.Point) (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hQ : addOrderOf Q = p) :
    Q.xc ^ 2 - W.a₄ ≠ 0 ∧ v (2 • Q).xc + 2 * v Q.xc = 2 * v (Q.xc ^ 2 - W.a₄) := by
  have hp1 : ¬ p ∣ 1 := Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
  have hQ0 : Q ≠ 0 := by
    intro hz
    exact hp1 (hQ ▸ addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by simpa using hz))
  have hD := tangent_denominator_exact_of_prime_order h₁ h₃ h₆ ha₂ ha₄ hγ Q p hp hp5 hQ
    (Point.eq_some_xc_yc hQ0)
  have h2x := nsmul_x_nonzero_of_prime_order h₁ h₃ h₆ Q p hp (by omega) hQ 2
    (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
  exact double_x_valuation_identity h₁ h₃ h₆ Q (Point.eq_some_xc_yc hQ0) hD h2x

/-- 2≤k≤p−2では差の分母も和差のxも非零であり、実際の(k±1)Qの付値漸化式が成立する。
分子の非零性も結論に含め、同値時のmin下界を後で安全に取り出せる形にする。 -/
theorem plus_minus_x_valuation_of_prime_order
    (h₁ : W.a₁ = 1) (h₃ : W.a₃ = 0) (h₆ : W.a₆ = 0)
    (Q : W.Point) (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hQ : addOrderOf Q = p)
    (k : ℕ) (hk2 : 2 ≤ k) (hkp : k ≤ p - 2) :
    (k • Q).xc ≠ Q.xc ∧ (k • Q).xc * Q.xc - W.a₄ ≠ 0 ∧
    v ((k + 1) • Q).xc + v ((k - 1) • Q).xc + 2 * v ((k • Q).xc - Q.xc) =
      2 * v ((k • Q).xc * Q.xc - W.a₄) := by
  have hp1 : ¬ p ∣ 1 := Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
  have hpk : ¬ p ∣ k := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hpplus : ¬ p ∣ k + 1 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hpminus : ¬ p ∣ k - 1 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hQ0 : Q ≠ 0 := by
    intro hz
    exact hp1 (hQ ▸ addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by simpa using hz))
  have hk0 : k • Q ≠ 0 := fun hz => hpk (hQ ▸ addOrderOf_dvd_iff_nsmul_eq_zero.mpr hz)
  have hx := nsmul_x_ne_x_of_prime_order Q p hp5 hQ k hk2 hkp
  have hsum : k • Q + Q = (k + 1) • Q := (succ_nsmul Q k).symm
  have hsub : k • Q - Q = (k - 1) • Q := by
    symm
    apply (eq_sub_iff_add_eq).mpr
    rw [← succ_nsmul, Nat.sub_add_cancel (by omega)]
  have hplus : (k • Q + Q).xc ≠ 0 := by
    rw [hsum]
    exact nsmul_x_nonzero_of_prime_order h₁ h₃ h₆ Q p hp (by omega) hQ (k + 1) hpplus
  have hminus : (k • Q - Q).xc ≠ 0 := by
    rw [hsub]
    exact nsmul_x_nonzero_of_prime_order h₁ h₃ h₆ Q p hp (by omega) hQ (k - 1) hpminus
  have hv := plus_minus_x_valuation_identity h₁ h₃ h₆ (k • Q) Q
    (Point.eq_some_xc_yc hk0) (Point.eq_some_xc_yc hQ0) hx hplus hminus
  rw [hsum, hsub] at hv
  exact ⟨hx, hv⟩

end DkMath.Lib.NumberTheory.WeierstrassTorsionIdentities
