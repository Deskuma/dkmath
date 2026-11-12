/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_FreyPackage_freyCurve_rational_p_torsion_eq_zero.lean, S04.Orbit.
Upstream blob: fe61fd5d4f94d55b5a9da38d1541903c84397df0
Modified for DkMath: use the independent finite-orbit minimum principle,
generalize the curve hypotheses, and retain the existing point coordinates.
-/

import DkMath.Lib.NumberTheory.WeierstrassNegativeValuation
import DkMath.Lib.NumberTheory.EllipticFunctionField
import DkMath.Lib.Algebra.FiniteOrbitMinimum

#print "file: DkMath.Lib.NumberTheory.WeierstrassTorsionValuation"

/-!
# 有限位数の軌道へ負付値の降下を適用する

局所計算`double_x_valuation_drop`と、群論`nsmul_nonnegative_of_double_drop`を結ぶ。
点群・倍点・既存の`Point.xc`を使い、仮想的な整数列を置かない。
無限遠点ではxc=0という既存の便宜値を使うが、その点を有限座標点とは見なさない。

素数p>2の位数なら、非零な倍点Rの2倍も非零であり、倍点公式の分母を確保できる。
従って全てのkQでx座標の付値は非負となる。これは付値0の排除ではない。
後続の単元付値の議論で初めて1以上という強い下界を証明する必要がある。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassTorsionValuation
open WeierstrassCurve WeierstrassCurve.Affine
open RationalTwoAdicBounds WeierstrassNegativeValuation
open DkMath.Lib.Algebra.FiniteOrbitMinimum
variable {W : Affine ℚ}

/-- x=0の有限点は2倍で零になるため、位数が2より大きい点のx座標は非零。
この結論には係数の付値も、位数の素数性も不要である。 -/
theorem x_nonzero_of_addOrder_eq (h₁ : W.a₁ = 1) (h₃ : W.a₃ = 0) (h₆ : W.a₆ = 0)
    (Q : W.Point) (n : ℕ) (hn : 2 < n) (hQ : addOrderOf Q = n)
    {x y : ℚ} {h : W.Nonsingular x y} (hxy : Q = Point.some x y h) : x ≠ 0 := by
  intro hx
  have heq := equation_of_normalized h₁ h₃ h₆ h
  rw [hx] at heq
  have hy : y = 0 := by nlinarith [sq_nonneg y]
  have hneg : y = W.negY x y := by
    rw [negY_of_normalized h₁ h₃, hx, hy]
    norm_num
  have h2 : (2 : ℕ) • Q = 0 := by
    rw [two_nsmul, hxy, Point.add_self_of_Y_eq hneg]
  have hd : n ∣ 2 := by
    rw [← hQ]
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr h2
  have := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

/-- 位数p>2の全倍点でxの2進付値は非負。
負なら倍点で値が厳密に下がるが、周期pの有限軌道内に最小値があるため矛盾する。 -/
theorem x_nonnegative_of_prime_order (h₁ : W.a₁ = 1) (h₃ : W.a₃ = 0) (h₆ : W.a₆ = 0)
    (ha₂ : Lower 0 W.a₂) (ha₄ : Lower 1 W.a₄)
    (Q : W.Point) (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) (hQ : addOrderOf Q = p)
    (k : ℕ) : 0 ≤ padicValRat 2 (k • Q).xc := by
  have hperiod : p • Q = 0 := hQ ▸ addOrderOf_nsmul_eq_zero Q
  apply nsmul_nonnegative_of_double_drop Q p hp.pos hperiod (fun R : W.Point => padicValRat 2 R.xc) _ k
  intro j hj
  rcases hR : j • Q with _ | ⟨x, y, h⟩
  · rw [hR] at hj
    change padicValRat 2 (0 : W.Point).xc < 0 at hj
    change padicValRat 2 (0 : ℚ) < 0 at hj
    simp only [padicValRat.zero, lt_self_iff_false] at hj
  · rw [hR] at hj
    change padicValRat 2 x < 0 at hj
    have hx : Exact (padicValRat 2 x) x := by
      refine ⟨?_, rfl⟩
      intro hx0
      rw [hx0, padicValRat.zero] at hj
      omega
    have hjp : ¬ p ∣ j := by
      intro hd
      have hz : j • Q = 0 := addOrderOf_dvd_iff_nsmul_eq_zero.mp (hQ ▸ hd)
      rw [hR] at hz
      exact Point.some_ne_zero h hz
    have hdouble : 2 • (j • Q) ≠ 0 := by
      intro hz
      have hd : p ∣ j * 2 := by
        rw [← hQ]
        apply addOrderOf_dvd_iff_nsmul_eq_zero.mpr
        simpa only [mul_nsmul] using hz
      rcases hp.dvd_mul.mp hd with h | h
      · exact hjp h
      · have := Nat.le_of_dvd (by decide : 0 < 2) h
        omega
    have hy : y ≠ W.negY x y := by
      intro hy
      apply hdouble
      rw [hR, two_nsmul, Point.add_self_of_Y_eq hy]
    obtain ⟨_, hv⟩ := double_x_valuation_drop h₁ h₃ h₆ ha₂ ha₄ h hx hj hy
    rw [two_nsmul, Point.add_self_of_Y_ne hy]
    change padicValRat 2 (W.addX x x (W.slope x x y y)) < padicValRat 2 x
    omega

/-- pがkを割らない倍点は再び位数pを持ち、その実際のx座標は非零である。
後続の付値の積・商公式に必要な非零条件を、元の点から供給する。 -/
theorem nsmul_x_nonzero_of_prime_order (h₁ : W.a₁ = 1) (h₃ : W.a₃ = 0) (h₆ : W.a₆ = 0)
    (Q : W.Point) (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) (hQ : addOrderOf Q = p)
    (k : ℕ) (hk : ¬ p ∣ k) : (k • Q).xc ≠ 0 := by
  have hcop : (addOrderOf Q).Coprime k := by
    rw [hQ]
    exact hp.coprime_iff_not_dvd.mpr hk
  have hord : addOrderOf (k • Q) = p := hcop.addOrderOf_nsmul.trans hQ
  have hne : k • Q ≠ 0 := fun hz => hk (hQ ▸ addOrderOf_dvd_iff_nsmul_eq_zero.mpr hz)
  exact x_nonzero_of_addOrder_eq h₁ h₃ h₆ (k • Q) p hp2 hord (Point.eq_some_xc_yc hne)

/-- 零座標を許す下界としても同じ結果を公開する。零点での深さを誤読しないためのAPI。 -/
theorem x_integral_of_prime_order (h₁ : W.a₁ = 1) (h₃ : W.a₃ = 0) (h₆ : W.a₆ = 0)
    (ha₂ : Lower 0 W.a₂) (ha₄ : Lower 1 W.a₄)
    (Q : W.Point) (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) (hQ : addOrderOf Q = p)
    (k : ℕ) : Lower 0 (k • Q).xc :=
  Or.inr (x_nonnegative_of_prime_order h₁ h₃ h₆ ha₂ ha₄ Q p hp hp2 hQ k)

end DkMath.Lib.NumberTheory.WeierstrassTorsionValuation
