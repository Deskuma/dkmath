/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_FreyPackage_freyCurve_rational_p_torsion_eq_zero.lean,
the min conditions, endpoint and arith_core application in S04.
Upstream blob: fe61fd5d4f94d55b5a9da38d1541903c84397df0
Modified for DkMath: define the integer data from the existing point coordinates, prove every
input using chapters 001-006, and apply the independent folded-orbit core.
-/

import DkMath.Lib.NumberTheory.WeierstrassTorsionIdentities
import DkMath.Lib.NumberTheory.FoldedValuationOrbit

#print "file: DkMath.Lib.NumberTheory.WeierstrassValuationOrbit"

/-!
# NOTE-030-007: 同じ点から整数折り返し核の全入力を作る

e,A,B,A₁を仮想的な整数列として仮定せず、同じ有理点Qの実際の座標から定義する。
区間・倍点・和差は前章までの定理から得る。min条件では分子・分母の非零性を先に使う。
(p−1)Q=−Qはx座標を保つので、周期の端点も同じeへ戻る。

一般の正規化モデルには実際に有理5-torsionが存在する。
排除にはγ=pv−4という追加の算術が必要であり、これが整数核での素数約分を可能にする。
最後の定理はこの形の係数付値を持つモデルのp倍零点を零と証明する。
Frey Sourceへの係数供給は別モジュールに置き、この一般LibはDkMath.FLTへ依存しない。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassValuationOrbit
open WeierstrassCurve WeierstrassCurve.Affine
open RationalTwoAdicBounds WeierstrassTorsionValuation WeierstrassTorsionBounds
open WeierstrassTorsionIdentities
local notation "v₂" => padicValRat 2
variable {W : Affine ℚ}

/-- e(k)=v₂(x(kQ))。k=0では既存xcの便宜値を使うが、区間条件は非自明な倍点だけに課す。 -/
def xValuation (Q : W.Point) (k : ℕ) : ℤ := v₂ (k • Q).xc

/-- A(k)=v₂(x(kQ)x(Q)−a₄)。数値的なmin則を使う前に中身の非零性を証明する。 -/
def productGapValuation (Q : W.Point) (k : ℕ) : ℤ := v₂ ((k • Q).xc * Q.xc - W.a₄)

/-- B(k)=v₂(x(kQ)−x(Q))。内部添字でx座標差が非零であることを別途供給する。 -/
def differenceValuation (Q : W.Point) (k : ℕ) : ℤ := v₂ ((k • Q).xc - Q.xc)

/-- A₁=v₂(x(Q)²−a₄)。倍点恒等式から非零性を得る同じ分子を使う。 -/
def squareGapValuation (Q : W.Point) : ℤ := v₂ (Q.xc ^ 2 - W.a₄)

/-- 実際のQから定義した四つの値に対する、整数核と同じ七条件。
この命題をproviderとして仮定するのではなく、下のorbit_conditionsで全て証明する。 -/
def OrbitConditions (Q : W.Point) (p : ℕ) (γ : ℤ) : Prop :=
  (∀ k, 1 ≤ k → k ≤ p - 1 → 1 ≤ xValuation Q k ∧ xValuation Q k ≤ γ - 1) ∧
  ((2 * xValuation Q 1 ≠ γ → squareGapValuation Q = min (2 * xValuation Q 1) γ) ∧
    (2 * xValuation Q 1 = γ → γ ≤ squareGapValuation Q)) ∧
  (xValuation Q 2 + 2 * xValuation Q 1 = 2 * squareGapValuation Q) ∧
  (∀ k, 2 ≤ k → k ≤ p - 2 →
    (xValuation Q k + xValuation Q 1 ≠ γ →
      productGapValuation Q k = min (xValuation Q k + xValuation Q 1) γ) ∧
    (xValuation Q k + xValuation Q 1 = γ → γ ≤ productGapValuation Q k)) ∧
  (∀ k, 2 ≤ k → k ≤ p - 2 →
    (xValuation Q k ≠ xValuation Q 1 →
      differenceValuation Q k = min (xValuation Q k) (xValuation Q 1)) ∧
    (xValuation Q k = xValuation Q 1 → xValuation Q 1 ≤ differenceValuation Q k)) ∧
  (∀ k, 2 ≤ k → k ≤ p - 2 →
    xValuation Q (k + 1) + xValuation Q (k - 1) + 2 * differenceValuation Q k =
      2 * productGapValuation Q k) ∧
  xValuation Q (p - 1) = xValuation Q 1

/-- pQ=0なら(p−1)Q=−Qであり、x座標を保つので端点の付値が一致する。
この群論的な等式には係数の付値・素数性・Qの非零性は不要である。 -/
theorem xValuation_endpoint (Q : W.Point) (p : ℕ) (hp1 : 1 ≤ p) (hQp : p • Q = 0) :
    xValuation Q (p - 1) = xValuation Q 1 := by
  have hh : (p - 1) • Q + Q = 0 := by
    rw [← succ_nsmul, Nat.sub_add_cancel hp1, hQp]
  have hn : (p - 1) • Q = -Q := eq_neg_of_add_eq_zero_left hh
  unfold xValuation
  rw [one_nsmul, hn]
  cases Q <;> rfl

/-- 同じ位数p≥5の点から、区間・min・倍点・和差・端点の全七条件を証明する。
一致付値の場合も分子・分母の非零性を使い、零の便宜的な付値で下界を捏造しない。 -/
theorem orbit_conditions (h₁ : W.a₁ = 1) (h₃ : W.a₃ = 0) (h₆ : W.a₆ = 0)
    (ha₂ : Lower 0 W.a₂) {γ : ℤ} (ha₄ : Exact γ W.a₄) (hγ : 1 ≤ γ)
    (Q : W.Point) (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hQ : addOrderOf Q = p) :
    OrbitConditions Q p γ := by
  have he1 : xValuation Q 1 = v₂ Q.xc := by simp only [xValuation, one_nsmul]
  have hx (k : ℕ) (hk : ¬ p ∣ k) : (k • Q).xc ≠ 0 :=
    nsmul_x_nonzero_of_prime_order h₁ h₃ h₆ Q p hp (by omega) hQ k hk
  have hxQ : Q.xc ≠ 0 := by
    simpa only [one_nsmul] using hx 1 (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
  have hD := double_x_valuation_of_prime_order h₁ h₃ h₆ ha₂ ha₄ hγ Q p hp hp5 hQ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk1 hkp
    exact nsmul_x_bounds_of_prime_order h₁ h₃ h₆ ha₂ ha₄ hγ Q p hp hp5 hQ k
      (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  · have hs : Exact (2 * xValuation Q 1) (Q.xc ^ 2) := by
      have hh := (exact_valuation hxQ).square
      rw [he1]
      convert hh using 1
      ring
    exact hs.sub_valuation_spec ha₄ hD.1
  · simpa only [xValuation, one_nsmul, squareGapValuation] using hD.2
  · intro k hk2 hkp
    have hK := plus_minus_x_valuation_of_prime_order h₁ h₃ h₆ Q p hp hp5 hQ k hk2 hkp
    have hprod : Exact (xValuation Q k + xValuation Q 1) ((k • Q).xc * Q.xc) := by
      rw [he1]
      exact (exact_valuation (hx k (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)))).mul
        (exact_valuation hxQ)
    exact hprod.sub_valuation_spec ha₄ hK.2.1
  · intro k hk2 hkp
    have hK := plus_minus_x_valuation_of_prime_order h₁ h₃ h₆ Q p hp hp5 hQ k hk2 hkp
    have hE1 : Exact (xValuation Q 1) Q.xc := by rw [he1]; exact exact_valuation hxQ
    exact (exact_valuation (hx k (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)))).sub_valuation_spec
      hE1 (sub_ne_zero.mpr hK.1)
  · intro k hk2 hkp
    exact (plus_minus_x_valuation_of_prime_order h₁ h₃ h₆ Q p hp hp5 hQ k hk2 hkp).2.2
  · exact xValuation_endpoint Q p (by omega) (hQ ▸ addOrderOf_nsmul_eq_zero Q)

/-- γ=pv−4という算術を加えると、実際の位数pの点の軌道は整数折り返し核と矛盾する。
七条件は全て同じQから証明し、素数の約分は既存の整数核へ委ねる。 -/
theorem no_prime_shifted_torsion (h₁ : W.a₁ = 1) (h₃ : W.a₃ = 0) (h₆ : W.a₆ = 0)
    (ha₂ : Lower 0 W.a₂) {γ : ℤ} (ha₄ : Exact γ W.a₄) (hγ : 1 ≤ γ)
    (Q : W.Point) (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hQ : addOrderOf Q = p)
    (v : ℤ) (hshift : γ = (p : ℤ) * v - 4) : False := by
  obtain ⟨hbd, hA₁, h2, hA, hB, hrec, hend⟩ := orbit_conditions h₁ h₃ h₆ ha₂ ha₄ hγ Q p hp hp5 hQ
  exact FoldedValuationOrbit.no_prime_shifted_valuation_orbit p hp hp5 v γ hshift
    (xValuation Q) (productGapValuation Q) (differenceValuation Q) (squareGapValuation Q)
    hbd hA₁ h2 hA hB hrec hend

/-- 正規化係数・正確な深さγ=pv−4を持つ有理モデルのp倍零点は零である。
非零点の位数pを素数性から導くため、位数や整数列のproviderを仮定しない。 -/
theorem prime_torsion_eq_zero (h₁ : W.a₁ = 1) (h₃ : W.a₃ = 0) (h₆ : W.a₆ = 0)
    (ha₂ : Lower 0 W.a₂) {γ : ℤ} (ha₄ : Exact γ W.a₄) (hγ : 1 ≤ γ)
    (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (v : ℤ) (hshift : γ = (p : ℤ) * v - 4)
    (Q : W.Point) (hQp : p • Q = 0) : Q = 0 := by
  by_contra hQ0
  have : Fact p.Prime := ⟨hp⟩
  exact no_prime_shifted_torsion h₁ h₃ h₆ ha₂ ha₄ hγ Q p hp hp5
    (addOrderOf_eq_prime hQp hQ0) v hshift

end DkMath.Lib.NumberTheory.WeierstrassValuationOrbit
