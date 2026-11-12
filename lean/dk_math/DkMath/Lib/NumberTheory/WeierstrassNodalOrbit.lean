/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from S_cyclotomic_velu_xLaw.lean (orbit finite sums),
blob 3070fac325fbd76952d37b988b13682b20dcadb4.
Modified: arbitrary-order, arbitrary-characteristic public API and actual nodal point sums.
-/

import DkMath.Lib.NumberTheory.WeierstrassNodalFrame
import Mathlib.Algebra.Ring.GeomSum

#print "file: DkMath.Lib.NumberTheory.WeierstrassNodalOrbit"

/-!
# 滑らかな節点核の座標和と冪写像

[DkMath.Lib] 節点比tcは実点の加法を乗法へ送る。原始n乗根ζで巡回する
z(tζʲ)の和を、有限等比和の二乗と根の冪和から計算する。
分母を払うと、二つの添字a,bのうちa+b+1=nの反対角線だけが残る。
これはn²という重みの由来であり、無限級数や解析的微分を使わない。

次に同じFrame・同じ実点P,Qを保ち、Qの平行移動軌道へ公式を適用する。
nP=Oとなる衝突軌道は有限点公式から除外し、巡回核への所属との同値で記録する。
この章は剰余曲線上の座標和の計算であり、一般ファイバーの商写像との還元可換性は
まだ結論しない。特に衝突点の付値計算とY座標の輸送は別に必要である。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassNodalOrbit
open Finset
open WeierstrassCurve WeierstrassCurve.Affine
open EllipticNodalTorsion.NodalTorsion
variable {K : Type*} [Field K] {n : ℕ} {ζ : K}

/-- [DkMath.Lib] 原始n乗根の冪和。nが指数を割る場合だけnが残る。
素数性・標数0は不要であり、後の二項有限和の直交性を担う。 -/
theorem root_power_sum (hζ : IsPrimitiveRoot ζ n) (m : ℕ) :
    ∑ j ∈ range n, (ζ ^ j) ^ m = if n ∣ m then (n : K) else 0 := by
  split_ifs with h
  · obtain ⟨c, rfl⟩ := h
    have h1 : ∀ j ∈ range n, (ζ ^ j) ^ (n * c) = 1 := fun j _ => by
      rw [← pow_mul, mul_comm j, mul_assoc, pow_mul, hζ.pow_eq_one, one_pow]
    rw [sum_congr rfl h1, sum_const, card_range, nsmul_eq_mul, mul_one]
  · have h1 : ζ ^ m ≠ 1 := fun e => h ((hζ.pow_eq_one_iff_dvd m).mp e)
    have h2 : (ζ ^ m) ^ n = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    calc ∑ j ∈ range n, (ζ ^ j) ^ m = ∑ j ∈ range n, (ζ ^ m) ^ j := by
          refine sum_congr rfl fun j _ => ?_
          rw [← pow_mul, ← pow_mul, mul_comm]
      _ = 0 := by
          have h3 := mul_neg_geom_sum (ζ ^ m) n
          rw [h2, sub_self] at h3
          exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr (Ne.symm h1))

private lemma orbit_numerator (hζ : IsPrimitiveRoot ζ n) (w : K) :
    ∑ j ∈ range n, w * ζ ^ j * (∑ i ∈ range n, (w * ζ ^ j) ^ i) ^ 2
      = (n : K) ^ 2 * w ^ n := by
  have hexp : ∀ j ∈ range n, w * ζ ^ j * (∑ i ∈ range n, (w * ζ ^ j) ^ i) ^ 2
      = ∑ a ∈ range n, ∑ b ∈ range n, (ζ ^ j) ^ (a + b + 1) * w ^ (a + b + 1) := by
    intro j _
    rw [sq, sum_mul_sum, mul_sum]
    refine sum_congr rfl fun a _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun b _ => ?_
    rw [← mul_pow]
    ring
  rw [sum_congr rfl hexp, sum_comm]
  have hinner : ∀ a ∈ range n,
      ∑ j ∈ range n, ∑ b ∈ range n, (ζ ^ j) ^ (a + b + 1) * w ^ (a + b + 1)
        = (n : K) * w ^ n := by
    intro a ha
    have ha' := mem_range.mp ha
    rw [sum_comm]
    have hb : ∀ b ∈ range n, ∑ j ∈ range n, (ζ ^ j) ^ (a + b + 1) * w ^ (a + b + 1)
        = if b = n - 1 - a then (n : K) * w ^ n else 0 := by
      intro b hb
      have hb' := mem_range.mp hb
      rw [← sum_mul, root_power_sum hζ]
      by_cases hab : b = n - 1 - a
      · have e : a + b + 1 = n := by omega
        rw [ite_eq_left (e ▸ dvd_refl n), ite_eq_left hab, e]
      · have hnd : ¬ n ∣ a + b + 1 := by
          rintro ⟨c, hc⟩
          have hc1 : n * c < n * 2 := by omega
          have hc2 : 0 < n * c := by omega
          have hc3 : c < 2 := Nat.lt_of_mul_lt_mul_left hc1
          have hc4 : 0 < c := Nat.pos_of_mul_pos_left hc2
          interval_cases c
          omega
        rw [ite_eq_right hnd, ite_eq_right hab, zero_mul]
    rw [sum_congr rfl hb, sum_ite_eq' (range n) (n - 1 - a) (fun _ => (n : K) * w ^ n),
      ite_eq_left (mem_range.mpr (by omega))]
  rw [sum_congr rfl hinner, sum_const, card_range, nsmul_eq_mul, sq, mul_assoc]

private lemma geom_orbit (hζ : IsPrimitiveRoot ζ n) (w : K) (j : ℕ) :
    (1 - w * ζ ^ j) * ∑ i ∈ range n, (w * ζ ^ j) ^ i = 1 - w ^ n := by
  rw [mul_neg_geom_sum, mul_pow, ← pow_mul, mul_comm j n, pow_mul, hζ.pow_eq_one, one_pow,
    mul_one]

private lemma one_sub_orbit_ne_zero (hζ : IsPrimitiveRoot ζ n) {w : K} (hw : w ^ n ≠ 1)
    (j : ℕ) : 1 - w * ζ ^ j ≠ 0 := by
  intro h0
  have hg := geom_orbit hζ w j
  rw [h0, zero_mul] at hg
  exact hw (sub_eq_zero.mp hg.symm).symm

/-- [DkMath.Lib] 節点の反転不変座標z(t)=t/(1−t)²の巡回軌道和はn²z(tⁿ)。
条件tⁿ≠1は軌道の全項が有限であることを保証する。nや2,3では割らないため、
小標数でも同じ式が成立する。 -/
theorem orbit_x_sum (hζ : IsPrimitiveRoot ζ n) {w : K} (hw : w ^ n ≠ 1) :
    ∑ j ∈ range n, w * ζ ^ j / (1 - w * ζ ^ j) ^ 2
      = (n : K) ^ 2 * w ^ n / (1 - w ^ n) ^ 2 := by
  have hD : (1 : K) - w ^ n ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  have hterm : ∀ j ∈ range n, w * ζ ^ j / (1 - w * ζ ^ j) ^ 2
      = w * ζ ^ j * (∑ i ∈ range n, (w * ζ ^ j) ^ i) ^ 2 / (1 - w ^ n) ^ 2 := by
    intro j _
    have hg := geom_orbit hζ w j
    have hv := one_sub_orbit_ne_zero hζ hw j
    rw [div_eq_div_iff (pow_ne_zero 2 hv) (pow_ne_zero 2 hD), ← hg]
    ring
  rw [sum_congr rfl hterm]
  simp_rw [div_eq_mul_inv]
  rw [← sum_mul, orbit_numerator hζ w]


variable [DecidableEq K] {W : WeierstrassCurve K} {x₀ y₀ α : K}

omit [DecidableEq K] in
/-- [DkMath.Lib] 分離した節点の比は全滑らかな実点上で単射。
二点の差の比が1なら、その差はOである。 -/
theorem tc_injective (F : Frame W x₀ y₀ α) (hsep : α ≠ -W.a₁ - α) :
    Function.Injective (tc W x₀ y₀ α) := by
  classical
  intro P Q h
  apply sub_eq_zero.mp
  apply eq_zero_of_tc_eq_one F hsep
  rw [sub_eq_add_neg, tc_add F, tc_neg F, h, mul_inv_cancel₀ (tc_ne_zero F Q)]

/-- [DkMath.Lib] 実点のn倍がOであることと、同じ節点比のn乗が1であることは同値。 -/
theorem nsmul_eq_zero_iff (F : Frame W x₀ y₀ α) (hsep : α ≠ -W.a₁ - α)
    (P : W.toAffine.Point) : n • P = 0 ↔ tc W x₀ y₀ α P ^ n = 1 := by
  rw [← tc_nsmul F]
  exact ⟨fun h => by rw [h, tc_zero], eq_zero_of_tc_eq_one F hsep _⟩

/-- [DkMath.Lib] 原始n乗根を比に持つ同じQは、節点の全n捩れを生成する。
これは剰余点群内での主張であり、一般ファイバーの核への持上げは主張しない。 -/
theorem nsmul_eq_zero_iff_mem_zmultiples (F : Frame W x₀ y₀ α)
    (hsep : α ≠ -W.a₁ - α) (hn : n ≠ 0) (Q : W.toAffine.Point)
    (hQ : IsPrimitiveRoot (tc W x₀ y₀ α Q) n) (P : W.toAffine.Point) :
    n • P = 0 ↔ P ∈ AddSubgroup.zmultiples Q := by
  let : NeZero n := ⟨hn⟩
  constructor
  · intro hP
    obtain ⟨j, -, hj⟩ := hQ.eq_pow_of_pow_eq_one ((nsmul_eq_zero_iff F hsep P).mp hP)
    have he : P = j • Q := tc_injective F hsep (by rw [tc_nsmul F]; exact hj.symm)
    rw [he]
    exact AddSubgroup.nsmul_mem_zmultiples Q j
  · intro hP
    obtain ⟨j, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hP
    have hkill : n • Q = 0 := (nsmul_eq_zero_iff F hsep Q).mpr hQ.pow_eq_one
    rw [smul_comm, hkill, smul_zero]

/-- [DkMath.Lib] 衝突しない同じ実点Pの巡回平行移動和。
Qの原始根性とnP≠Oから全てのP+jQ≠Oを内部供給し、Oの便宜座標を使わない。 -/
theorem translated_x_sum (F : Frame W x₀ y₀ α) (hsep : α ≠ -W.a₁ - α)
    (P Q : W.toAffine.Point) (hQ : IsPrimitiveRoot (tc W x₀ y₀ α Q) n)
    (hP : n • P ≠ 0) :
    ∑ j ∈ range n, (P + j • Q).xc =
      (n : K) * x₀ + (2 * α + W.a₁) ^ 2 *
        ((n : K) ^ 2 * tc W x₀ y₀ α P ^ n / (1 - tc W x₀ y₀ α P ^ n) ^ 2) := by
  have ht : tc W x₀ y₀ α P ^ n ≠ 1 := mt (nsmul_eq_zero_iff F hsep P).mpr hP
  have he : ∀ j ∈ range n, (P + j • Q).xc =
      x₀ + (2 * α + W.a₁) ^ 2 *
        ((tc W x₀ y₀ α P * tc W x₀ y₀ α Q ^ j) /
          (1 - tc W x₀ y₀ α P * tc W x₀ y₀ α Q ^ j) ^ 2) := by
    intro j _
    have hn := one_sub_orbit_ne_zero hQ ht j
    have hpq : P + j • Q ≠ 0 := by
      intro h
      apply hn
      have hh := congrArg (tc W x₀ y₀ α) h
      rw [tc_add F, tc_nsmul F, tc_zero] at hh
      exact sub_eq_zero.mpr hh.symm
    simpa only [tc_add F, tc_nsmul F] using WeierstrassNodalFrame.xc_eq F hsep _ hpq
  rw [sum_congr rfl he, sum_add_distrib, sum_const, card_range, nsmul_eq_mul,
    ← mul_sum, orbit_x_sum hQ ht]

/-- [DkMath.Lib] 同じ実点のn倍で巡回座標和を読む。
冪写像に対応するxの重みはn²であり、中心x₀の補正も明示する。 -/
theorem translated_x_sum_nsmul (F : Frame W x₀ y₀ α) (hsep : α ≠ -W.a₁ - α)
    (P Q : W.toAffine.Point) (hQ : IsPrimitiveRoot (tc W x₀ y₀ α Q) n)
    (hP : n • P ≠ 0) :
    ∑ j ∈ range n, (P + j • Q).xc =
      (n : K) * x₀ + (n : K) ^ 2 * ((n • P).xc - x₀) := by
  rw [translated_x_sum F hsep P Q hQ hP, WeierstrassNodalFrame.xc_eq F hsep _ hP,
    tc_nsmul F]
  ring

/-- [DkMath.Lib] Véluの正規化と同じ「平行移動和−核座標和」を冪写像へ変換する。
静的な核座標和を残すことで12の逆数を要求せず、標数2,3も扱う。 -/
theorem normalized_x_sum (F : Frame W x₀ y₀ α) (hsep : α ≠ -W.a₁ - α)
    (P Q : W.toAffine.Point) (hQ : IsPrimitiveRoot (tc W x₀ y₀ α Q) n)
    (hP : n • P ≠ 0) :
    (∑ j ∈ range n, (P + j • Q).xc) - (∑ j ∈ range n, (j • Q).xc) =
      (n : K) ^ 2 * (n • P).xc + ((n : K) - (n : K) ^ 2) * x₀ -
        ∑ j ∈ range n, (j • Q).xc := by
  rw [translated_x_sum_nsmul F hsep P Q hQ hP]
  ring

end DkMath.Lib.NumberTheory.WeierstrassNodalOrbit
