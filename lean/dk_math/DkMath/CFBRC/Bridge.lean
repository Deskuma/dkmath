/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CFBRC.Basic
import DkMath.CFBRC.CyclotomicProduct
import DkMath.NumberTheory.Gcd.GN

/-!
# CFBRC Bridge

`cyclotomicPrimeCore` と Zsigmondy / valuation 層（`DkMath.NumberTheory.Gcd.*`）
を接続する再利用 API。
-/

namespace DkMath.CFBRC

open DkMath.CosmicFormulaBinom

/--
差冪と core の除法同値（Nat 版）。

前提 `q ∤ x` の下で、
`q ∣ ((x+u)^p - u^p)` と `q ∣ cyclotomicPrimeCore p x u` は同値になる。
差冪分解 `((x+u)^p-u^p)=x*core` と素数の積除法判定を使う基本橋渡し。
-/
theorem prime_dvd_sub_pow_iff_dvd_cyclotomicPrimeCore_nat
    {p x u q : ℕ}
    (hq : Nat.Prime q) (hq_not_dvd_x : ¬ q ∣ x) :
    q ∣ ((x + u) ^ p - u ^ p) ↔ q ∣ cyclotomicPrimeCore p x u := by
  constructor
  · intro hsub
    exact prime_dvd_cyclotomicPrimeCore_of_dvd_sub_not_dvd_left
      (p := p) (x := x) (u := u) (q := q) hq hsub hq_not_dvd_x
  · intro hcore
    have hmul : q ∣ x * cyclotomicPrimeCore p x u := dvd_mul_of_dvd_right hcore x
    simpa [sub_eq_mul_cyclotomicPrimeCore_nat p x u] using hmul

/--
deprecated alias.

`CyclotomicProduct` 側の標準名
`cyclotomicDivisorsProductShifted_eq_GN_of_ne_zero`
へ移行するための互換エントリ。
-/
@[deprecated cyclotomicDivisorsProductShifted_eq_GN_of_ne_zero
  (since := "2026-03-12")]
theorem cyclotomicDivisorsProductShifted_eq_GN_of_ne_zero_bridge
    {R : Type _} [Field R] {d : ℕ} (hd : 0 < d)
    {x u : R} (hx : x ≠ 0) (hu : u ≠ 0) :
    cyclotomicDivisorsProductShifted d x u = GN d x u :=
  cyclotomicDivisorsProductShifted_eq_GN_of_ne_zero (R := R) hd hx hu

/--
Zsigmondy 層A（prime exponent）からの存在橋渡し（差分形）。

`a:=x+u, b:=u` と置き、`d` 素数指数で `d ∤ x` のとき、
`(x+u)^d-u^d` を割る原始素因子 `q`（低次差分は割らない）を返す。
CFBRC 記法に揃えた公開 API。
-/
theorem exists_primitive_prime_factor_sub_pow_of_prime_exp_boundary
    {d x u : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime (x + u) u)
    (hpnd : ¬ d ∣ x) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ ((x + u) ^ d - u ^ d) ∧ ¬ q ∣ x ∧
      (∀ {k : ℕ}, 0 < k → k < d → ¬ q ∣ ((x + u) ^ k - u ^ k)) := by
  have hab_lt : u < x + u := by omega
  rcases DkMath.NumberTheory.GcdNext.exists_primitive_prime_factor_basic
      (a := x + u) (b := u) (d := d)
      hd_prime hd_ge hab_lt hu hcop (by simpa [Nat.add_sub_cancel] using hpnd) with
    ⟨q, hqP, hq_dvd_diff, hq_ndvd_gap⟩
  have hd1 : 1 < d := lt_of_lt_of_le (by decide : 1 < 3) hd_ge
  have hprim :
      ∀ {k : ℕ}, 0 < k → k < d → ¬ q ∣ ((x + u) ^ k - u ^ k) :=
    DkMath.NumberTheory.GcdNext.prime_exp_not_dvd_diff_imp_primitive
      (a := x + u) (b := u) (d := d) (q := q)
      hd_prime hd1 hqP hcop hab_lt hu hq_dvd_diff hq_ndvd_gap
  refine ⟨q, hqP, hq_dvd_diff, ?_, hprim⟩
  simpa [Nat.add_sub_cancel] using hq_ndvd_gap

/--
Zsigmondy 存在結果の core 直結版（prime exponent）。

同じ原始素因子 `q` が `cyclotomicPrimeCore d x u` を割る形に変換して返す。
`prime_dvd_sub_pow_iff_dvd_cyclotomicPrimeCore_nat` を通じた除法同値を使用。
-/
theorem exists_primitive_prime_factor_dvd_cyclotomicPrimeCore_of_prime_exp_boundary
    {d x u : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime (x + u) u)
    (hpnd : ¬ d ∣ x) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ cyclotomicPrimeCore d x u ∧ ¬ q ∣ x ∧
      (∀ {k : ℕ}, 0 < k → k < d → ¬ q ∣ ((x + u) ^ k - u ^ k)) := by
  rcases exists_primitive_prime_factor_sub_pow_of_prime_exp_boundary
      (d := d) (x := x) (u := u) hd_prime hd_ge hx hu hcop hpnd with
    ⟨q, hqP, hq_dvd_diff, hq_ndvd_x, hprim⟩
  have hq_dvd_core : q ∣ cyclotomicPrimeCore d x u :=
    (prime_dvd_sub_pow_iff_dvd_cyclotomicPrimeCore_nat
      (p := d) (x := x) (u := u) (q := q) hqP hq_ndvd_x).1 hq_dvd_diff
  exact ⟨q, hqP, hq_dvd_core, hq_ndvd_x, hprim⟩

/--
`Nat.Coprime x u` 前提に正規化した差分形 wrapper。

内部で `Nat.Coprime (x+u) u` へ変換し、
Zsigmondy 存在 API（差分形）へ委譲する。
-/
theorem exists_primitive_prime_factor_sub_pow_of_prime_exp_boundary_of_coprime
    {d x u : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : ¬ d ∣ x) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ ((x + u) ^ d - u ^ d) ∧ ¬ q ∣ x ∧
      (∀ {k : ℕ}, 0 < k → k < d → ¬ q ∣ ((x + u) ^ k - u ^ k)) := by
  exact exists_primitive_prime_factor_sub_pow_of_prime_exp_boundary
    (d := d) (x := x) (u := u) hd_prime hd_ge hx hu
    ((Nat.coprime_add_self_left).2 hcop) hpnd

/--
`Nat.Coprime x u` 前提に正規化した core 形 wrapper。

内部で `Nat.Coprime (x+u) u` へ変換し、
Zsigmondy 存在 API（core 除法形）へ委譲する。
-/
theorem exists_primitive_prime_factor_dvd_cyclotomicPrimeCore_of_prime_exp_boundary_of_coprime
    {d x u : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : ¬ d ∣ x) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ cyclotomicPrimeCore d x u ∧ ¬ q ∣ x ∧
      (∀ {k : ℕ}, 0 < k → k < d → ¬ q ∣ ((x + u) ^ k - u ^ k)) := by
  exact exists_primitive_prime_factor_dvd_cyclotomicPrimeCore_of_prime_exp_boundary
    (d := d) (x := x) (u := u) hd_prime hd_ge hx hu
    ((Nat.coprime_add_self_left).2 hcop) hpnd

/--
境界 side の指定子。

`right`: 基準境界を `u` とする（`(x+u)^d-u^d`）。
`left`: 基準境界を `x` とする（`(x+u)^d-x^d`）。
-/
inductive BoundarySide where
  | right
  | left
deriving DecidableEq, Repr

/--
side 指定に応じた差分式（valuation の入力）。

`right` では `((x+u)^d-u^d)`、`left` では `((x+u)^d-x^d)` を返す。
-/
@[simp] def boundaryDiffPow (side : BoundarySide) (d x u : ℕ) : ℕ :=
  match side with
  | .right => (x + u) ^ d - u ^ d
  | .left => (x + u) ^ d - x ^ d

/--
side 指定に応じた `GN` 接続先。

`right` では `GN d x u`、`left` では対称形 `GN d u x`。
-/
@[simp] def boundaryGN (side : BoundarySide) (d x u : ℕ) : ℕ :=
  match side with
  | .right => GN d x u
  | .left => GN d u x

/--
side 指定に応じた `cyclotomicPrimeCore` 接続先。

`right` では `core d x u`、`left` では対称形 `core d u x`。
-/
@[simp] def boundaryCyclotomicPrimeCore (side : BoundarySide) (d x u : ℕ) : ℕ :=
  match side with
  | .right => cyclotomicPrimeCore d x u
  | .left => cyclotomicPrimeCore d u x

/--
valuation bridge（GN 版, 右境界）。

前提 `q ∤ x` の下で
`padicValNat q ((x+u)^d-u^d) = padicValNat q (GN d x u)` を与える。
`Gcd.GN` 層の gap 版定理を CFBRC 境界記法へ移したもの。
-/
theorem padicValNat_sub_pow_eq_padicValNat_GN_of_not_dvd_boundary
    {d x u q : ℕ}
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hqP : Nat.Prime q) (hq_not_dvd_x : ¬ q ∣ x) :
    padicValNat q ((x + u) ^ d - u ^ d) =
      padicValNat q (GN d x u) := by
  have hval_gap :=
    DkMath.NumberTheory.Gcd.padicValNat_sub_pow_eq_padicValNat_GN_of_not_dvd_gap
      (p := d) (z := x + u) (y := u) (q := q)
      hd2 (by omega) hu hqP
      (by simpa [Nat.add_sub_cancel_left] using hq_not_dvd_x)
  simpa [Nat.add_sub_cancel_left] using hval_gap

/--
valuation bridge の前提正規化 wrapper（GN 版, 右境界）。

`Nat.Coprime x u` と `q ∣ u` から `¬ q ∣ x` を導出し、
`..._of_not_dvd_boundary` を直接使える形に落とす。
-/
theorem padicValNat_sub_pow_eq_padicValNat_GN_of_coprime_of_dvd_right
    {d x u q : ℕ}
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hcop : Nat.Coprime x u) (hqP : Nat.Prime q) (hq_dvd_u : q ∣ u) :
    padicValNat q ((x + u) ^ d - u ^ d) =
      padicValNat q (GN d x u) := by
  have hq_not_dvd_x : ¬ q ∣ x := by
    intro hq_dvd_x
    have hq_dvd_gcd : q ∣ Nat.gcd x u := Nat.dvd_gcd hq_dvd_x hq_dvd_u
    rw [hcop.gcd_eq_one] at hq_dvd_gcd
    exact Nat.Prime.not_dvd_one hqP hq_dvd_gcd
  exact padicValNat_sub_pow_eq_padicValNat_GN_of_not_dvd_boundary
    (d := d) (x := x) (u := u) (q := q) hd2 hx hu hqP hq_not_dvd_x

/--
valuation bridge（core 版, 右境界）。

前提 `q ∤ x` の下で
`padicValNat q ((x+u)^p-u^p) = padicValNat q (cyclotomicPrimeCore p x u)`。
GN 版評価と `cyclotomicPrimeCore = GN`（Nat, `x>0`）を合成して得る。
-/
theorem padicValNat_sub_pow_eq_padicValNat_cyclotomicPrimeCore_of_not_dvd_boundary
    {p x u q : ℕ}
    (hp2 : 2 ≤ p) (hx : 0 < x) (hu : 0 < u)
    (hqP : Nat.Prime q) (hq_not_dvd_x : ¬ q ∣ x) :
    padicValNat q ((x + u) ^ p - u ^ p) =
      padicValNat q (cyclotomicPrimeCore p x u) := by
  have hval_GN :
      padicValNat q ((x + u) ^ p - u ^ p) = padicValNat q (GN p x u) := by
    exact padicValNat_sub_pow_eq_padicValNat_GN_of_not_dvd_boundary
      (d := p) (x := x) (u := u) (q := q) hp2 hx hu hqP hq_not_dvd_x
  have hcore_eq_GN : cyclotomicPrimeCore p x u = GN p x u :=
    cyclotomicPrimeCore_eq_GN_nat (p := p) (x := x) (u := u) hx
  calc
    padicValNat q ((x + u) ^ p - u ^ p) = padicValNat q (GN p x u) := hval_GN
    _ = padicValNat q (cyclotomicPrimeCore p x u) := by
      rw [hcore_eq_GN]

/--
valuation bridge の前提正規化 wrapper（core 版, 右境界）。

`Nat.Coprime x u` と `q ∣ u` から `¬ q ∣ x` を導出し、
core 版 valuation bridge へ接続する。
-/
theorem padicValNat_sub_pow_eq_padicValNat_cyclotomicPrimeCore_of_coprime_of_dvd_right
    {p x u q : ℕ}
    (hp2 : 2 ≤ p) (hx : 0 < x) (hu : 0 < u)
    (hcop : Nat.Coprime x u) (hqP : Nat.Prime q) (hq_dvd_u : q ∣ u) :
    padicValNat q ((x + u) ^ p - u ^ p) =
      padicValNat q (cyclotomicPrimeCore p x u) := by
  have hq_not_dvd_x : ¬ q ∣ x := by
    intro hq_dvd_x
    have hq_dvd_gcd : q ∣ Nat.gcd x u := Nat.dvd_gcd hq_dvd_x hq_dvd_u
    rw [hcop.gcd_eq_one] at hq_dvd_gcd
    exact Nat.Prime.not_dvd_one hqP hq_dvd_gcd
  exact padicValNat_sub_pow_eq_padicValNat_cyclotomicPrimeCore_of_not_dvd_boundary
    (p := p) (x := x) (u := u) (q := q) hp2 hx hu hqP hq_not_dvd_x

/--
valuation bridge の前提正規化 wrapper（GN 版, 左境界=対称版）。

`Nat.Coprime x u` と `q ∣ x` から `¬ q ∣ u` を導出し、
変数入替えで `((x+u)^d-x^d)` を `GN d u x` 側に接続する。
-/
theorem padicValNat_sub_pow_eq_padicValNat_GN_of_coprime_of_dvd_left
    {d x u q : ℕ}
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hcop : Nat.Coprime x u) (hqP : Nat.Prime q) (hq_dvd_x : q ∣ x) :
    padicValNat q ((x + u) ^ d - x ^ d) =
      padicValNat q (GN d u x) := by
  have hq_not_dvd_u : ¬ q ∣ u := by
    intro hq_dvd_u
    have hq_dvd_gcd : q ∣ Nat.gcd x u := Nat.dvd_gcd hq_dvd_x hq_dvd_u
    rw [hcop.gcd_eq_one] at hq_dvd_gcd
    exact Nat.Prime.not_dvd_one hqP hq_dvd_gcd
  have hswap :
      padicValNat q ((u + x) ^ d - x ^ d) =
        padicValNat q (GN d u x) :=
    padicValNat_sub_pow_eq_padicValNat_GN_of_not_dvd_boundary
      (d := d) (x := u) (u := x) (q := q) hd2 hu hx hqP hq_not_dvd_u
  simpa [Nat.add_comm] using hswap

/--
valuation bridge の前提正規化 wrapper（core 版, 左境界=対称版）。

`Nat.Coprime x u` と `q ∣ x` から `¬ q ∣ u` を導出し、
変数入替えで `((x+u)^p-x^p)` を `core p u x` 側に接続する。
-/
theorem padicValNat_sub_pow_eq_padicValNat_cyclotomicPrimeCore_of_coprime_of_dvd_left
    {p x u q : ℕ}
    (hp2 : 2 ≤ p) (hx : 0 < x) (hu : 0 < u)
    (hcop : Nat.Coprime x u) (hqP : Nat.Prime q) (hq_dvd_x : q ∣ x) :
    padicValNat q ((x + u) ^ p - x ^ p) =
      padicValNat q (cyclotomicPrimeCore p u x) := by
  have hq_not_dvd_u : ¬ q ∣ u := by
    intro hq_dvd_u
    have hq_dvd_gcd : q ∣ Nat.gcd x u := Nat.dvd_gcd hq_dvd_x hq_dvd_u
    rw [hcop.gcd_eq_one] at hq_dvd_gcd
    exact Nat.Prime.not_dvd_one hqP hq_dvd_gcd
  have hswap :
      padicValNat q ((u + x) ^ p - x ^ p) =
        padicValNat q (cyclotomicPrimeCore p u x) :=
    padicValNat_sub_pow_eq_padicValNat_cyclotomicPrimeCore_of_not_dvd_boundary
      (p := p) (x := u) (u := x) (q := q) hp2 hu hx hqP hq_not_dvd_u
  simpa [Nat.add_comm] using hswap

/--
高位 API（GN 版, side 指定）。

`BoundarySide` と gap 非除法前提
`match side with | right => ¬ q ∣ x | left => ¬ q ∣ u`
を受け取り、左右個別の `..._of_not_dvd_boundary` を一つの入口に統合する。
-/
theorem padicValNat_boundaryDiffPow_eq_boundaryGN_of_not_dvd_gap
    (side : BoundarySide) {d x u q : ℕ}
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : match side with
      | .right => ¬ q ∣ x
      | .left => ¬ q ∣ u) :
    padicValNat q (boundaryDiffPow side d x u) =
      padicValNat q (boundaryGN side d x u) := by
  cases side with
  | right =>
      simpa [boundaryDiffPow, boundaryGN] using
        (padicValNat_sub_pow_eq_padicValNat_GN_of_not_dvd_boundary
          (d := d) (x := x) (u := u) (q := q) hd2 hx hu hqP hq_not_dvd_gap)
  | left =>
      have hswap :
          padicValNat q ((u + x) ^ d - x ^ d) =
            padicValNat q (GN d u x) :=
        padicValNat_sub_pow_eq_padicValNat_GN_of_not_dvd_boundary
          (d := d) (x := u) (u := x) (q := q) hd2 hu hx hqP hq_not_dvd_gap
      simpa [boundaryDiffPow, boundaryGN, Nat.add_comm] using hswap

/--
高位 API（core 版, side 指定）。

`BoundarySide` と gap 非除法前提
`match side with | right => ¬ q ∣ x | left => ¬ q ∣ u`
を受け取り、左右個別の core valuation bridge を一つの入口に統合する。
-/
theorem padicValNat_boundaryDiffPow_eq_boundaryCyclotomicPrimeCore_of_not_dvd_gap
    (side : BoundarySide) {d x u q : ℕ}
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : match side with
      | .right => ¬ q ∣ x
      | .left => ¬ q ∣ u) :
    padicValNat q (boundaryDiffPow side d x u) =
      padicValNat q (boundaryCyclotomicPrimeCore side d x u) := by
  cases side with
  | right =>
      simpa [boundaryDiffPow, boundaryCyclotomicPrimeCore] using
        (padicValNat_sub_pow_eq_padicValNat_cyclotomicPrimeCore_of_not_dvd_boundary
          (p := d) (x := x) (u := u) (q := q) hd2 hx hu hqP hq_not_dvd_gap)
  | left =>
      have hswap :
          padicValNat q ((u + x) ^ d - x ^ d) =
            padicValNat q (cyclotomicPrimeCore d u x) :=
        padicValNat_sub_pow_eq_padicValNat_cyclotomicPrimeCore_of_not_dvd_boundary
          (p := d) (x := u) (u := x) (q := q) hd2 hu hx hqP hq_not_dvd_gap
      simpa [boundaryDiffPow, boundaryCyclotomicPrimeCore, Nat.add_comm] using hswap

/--
高位 API（GN 版, side 指定）。

`BoundarySide` と境界除法前提
`match side with | right => q ∣ u | left => q ∣ x`
を受け取り、`Nat.Coprime x u` から gap 非除法へ正規化して
`padicValNat_boundaryDiffPow_eq_boundaryGN_of_not_dvd_gap` に接続する。
-/
theorem padicValNat_boundaryDiffPow_eq_boundaryGN_of_coprime_of_dvd_boundary
    (side : BoundarySide) {d x u q : ℕ}
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hcop : Nat.Coprime x u) (hqP : Nat.Prime q)
    (hq_dvd_boundary : match side with
      | .right => q ∣ u
      | .left => q ∣ x) :
    padicValNat q (boundaryDiffPow side d x u) =
      padicValNat q (boundaryGN side d x u) := by
  cases side with
  | right =>
      have hq_not_dvd_gap : ¬ q ∣ x := by
        intro hq_dvd_x
        have hq_dvd_gcd : q ∣ Nat.gcd x u := Nat.dvd_gcd hq_dvd_x hq_dvd_boundary
        rw [hcop.gcd_eq_one] at hq_dvd_gcd
        exact Nat.Prime.not_dvd_one hqP hq_dvd_gcd
      exact padicValNat_boundaryDiffPow_eq_boundaryGN_of_not_dvd_gap
        (.right) (d := d) (x := x) (u := u) (q := q) hd2 hx hu hqP hq_not_dvd_gap
  | left =>
      have hq_not_dvd_gap : ¬ q ∣ u := by
        intro hq_dvd_u
        have hq_dvd_gcd : q ∣ Nat.gcd x u := Nat.dvd_gcd hq_dvd_boundary hq_dvd_u
        rw [hcop.gcd_eq_one] at hq_dvd_gcd
        exact Nat.Prime.not_dvd_one hqP hq_dvd_gcd
      exact padicValNat_boundaryDiffPow_eq_boundaryGN_of_not_dvd_gap
        (.left) (d := d) (x := x) (u := u) (q := q) hd2 hx hu hqP hq_not_dvd_gap

/--
高位 API（core 版, side 指定）。

`BoundarySide` と境界除法前提を受け取り、
`Nat.Coprime x u` から gap 非除法へ正規化して
`padicValNat_boundaryDiffPow_eq_boundaryCyclotomicPrimeCore_of_not_dvd_gap`
に接続する。
-/
theorem padicValNat_boundaryDiffPow_eq_boundaryCyclotomicPrimeCore_of_coprime_of_dvd_boundary
    (side : BoundarySide) {d x u q : ℕ}
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hcop : Nat.Coprime x u) (hqP : Nat.Prime q)
    (hq_dvd_boundary : match side with
      | .right => q ∣ u
      | .left => q ∣ x) :
    padicValNat q (boundaryDiffPow side d x u) =
      padicValNat q (boundaryCyclotomicPrimeCore side d x u) := by
  cases side with
  | right =>
      have hq_not_dvd_gap : ¬ q ∣ x := by
        intro hq_dvd_x
        have hq_dvd_gcd : q ∣ Nat.gcd x u := Nat.dvd_gcd hq_dvd_x hq_dvd_boundary
        rw [hcop.gcd_eq_one] at hq_dvd_gcd
        exact Nat.Prime.not_dvd_one hqP hq_dvd_gcd
      exact padicValNat_boundaryDiffPow_eq_boundaryCyclotomicPrimeCore_of_not_dvd_gap
        (.right) (d := d) (x := x) (u := u) (q := q) hd2 hx hu hqP hq_not_dvd_gap
  | left =>
      have hq_not_dvd_gap : ¬ q ∣ u := by
        intro hq_dvd_u
        have hq_dvd_gcd : q ∣ Nat.gcd x u := Nat.dvd_gcd hq_dvd_boundary hq_dvd_u
        rw [hcop.gcd_eq_one] at hq_dvd_gcd
        exact Nat.Prime.not_dvd_one hqP hq_dvd_gcd
      exact padicValNat_boundaryDiffPow_eq_boundaryCyclotomicPrimeCore_of_not_dvd_gap
        (.left) (d := d) (x := x) (u := u) (q := q) hd2 hx hu hqP hq_not_dvd_gap

end DkMath.CFBRC
