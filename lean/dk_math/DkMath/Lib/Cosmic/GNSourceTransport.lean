/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GNPhaseFactorization

/-!
# GN source 保存原理

GN の一つの線形因子を、係数と位相を明示して環準同型で運ぶ。
根だけを置き換える操作と、係数を含む source 全体の像を区別する。
係数環の拡大は多項式の等式を保存するが、整数への降下を供給しない。
-/

namespace DkMath.Lib.Cosmic

/-- GN の位相 ξ における線形 source。次数や原始性に依存しない。 -/
def phaseSource {R : Type*} [CommRing R] (ξ x u : R) : R := x + (1 - ξ) * u

/-- 二つの端点 a,b の差 `a-ξ*b` を、gap 座標 `x=a-b,u=b` で表す。 -/
theorem phaseSource_sub_coordinates {R : Type*} [CommRing R] (ξ a b : R) :
    phaseSource ξ (a - b) b = a - ξ * b := by
  unfold phaseSource
  ring

/-- 環準同型は source 全体を保存する。根だけでなく両係数も同時に写す。 -/
theorem map_phaseSource {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (ξ x u : R) :
    f (phaseSource ξ x u) = phaseSource (f ξ) (f x) (f u) := by
  simp only [phaseSource, map_add, map_mul, map_sub, map_one]

/-- 根を ζ^k へ送る写像は、位相添字 i を k*i へ送る。
係数 f(x),f(u) は一般には元の係数と異なる。 -/
theorem map_phaseSource_pow {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (ζ : R) (η : S) (x u : R) (k i : ℕ) (hζ : f ζ = η ^ k) :
    f (phaseSource (ζ ^ i) x u) = phaseSource (η ^ (k * i)) (f x) (f u) := by
  rw [map_phaseSource, map_pow, hζ, ← pow_mul]

/-- 係数を固定する写像の場合に限り、係数を変えない添字変換として書ける。 -/
theorem map_phaseSource_pow_of_fixed {R : Type*} [CommRing R]
    (f : R →+* R) (ζ x u : R) (k i : ℕ)
    (hζ : f ζ = ζ ^ k) (hx : f x = x) (hu : f u = u) :
    f (phaseSource (ζ ^ i) x u) = phaseSource (ζ ^ (k * i)) x u := by
  rw [map_phaseSource_pow f ζ ζ x u k i hζ, hx, hu]

/-- 位相添字の変換を元へ戻すには、根の次数を法とした指数の一致が必要。
この補題は係数を変えず、同じ根の冪だけを再添字付けする。 -/
theorem phaseSource_eq_of_pow_modEq {R : Type*} [CommRing R]
    {ζ : R} {n i j : ℕ} (hζ : ζ ^ n = 1) (hij : i ≡ j [MOD n]) (x u : R) :
    phaseSource (ζ ^ i) x u = phaseSource (ζ ^ j) x u := by
  have hi : ζ ^ i = ζ ^ (i % n) := by
    conv_lhs => rw [← Nat.mod_add_div i n]
    rw [pow_add, pow_mul, hζ, one_pow, mul_one]
  have hj : ζ ^ j = ζ ^ (j % n) := by
    conv_lhs => rw [← Nat.mod_add_div j n]
    rw [pow_add, pow_mul, hζ, one_pow, mul_one]
  rw [hi, hj, hij]

/-- 非零パラメータでは位相だけを変えても同じ source にはならない。
全積の保存と、一つの選ばれた因子の保存を区別するための検査である。 -/
theorem phaseSource_eq_iff_phase_eq {R : Type*} [CommRing R] [IsDomain R]
    (ξ η x u : R) (hu : u ≠ 0) :
    phaseSource ξ x u = phaseSource η x u ↔ ξ = η := by
  simp only [phaseSource, add_right_inj, mul_left_inj' hu, sub_right_inj]

end DkMath.Lib.Cosmic
