/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GNSuccessor
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.RingTheory.Coprime.Lemmas

#print "file: DkMath.Lib.Cosmic.GNSupport"

/-!
# Common divisors of adjacent gap-normalized kernels

Every common divisor divides both coordinate powers. A primitive coordinate
pair therefore gives coprime adjacent kernels. For degrees at least two,
common prime support is exactly the support shared by the two coordinates.
This is an adjacent-degree statement and gives no primitive-prime theorem.

## 教科書としての読み方

[DkMath.Lib] GN-LIB-001として既存の一般核を移管した。
namespaceは `DkMath.NumberTheory.GapFocusing` を維持するが、証明の所有者は
このLibモジュールである。旧importからも同じ定理へ到達できる。

共通約数を二つの再帰へ代入すると、`u^d` と `(x+u)^d` の両方を割る。
自然数の原始対では共通素数を座標へ戻し、一般可換環では座標冪のBézout関係を
隣接GNへ戻す。この二経路を分けることで、素因数分解を一般環へ持ち込まない。

素数の存在を述べる定理には正次数・正座標・原始性を残す。
その素数が直前の次数にないことだけを保証し、全過去次数での非出現や
付値1、完全冪の排除は追加しない。次数2以上での逆向きには下限を残す。

-/

namespace DkMath.NumberTheory.GapFocusing

open DkMath.CosmicFormula

/--
[DkMath.Lib] 昇格元: `DkMath.NumberTheory.GapFocusing.dvd_anchor_pow_of_dvd_adjacent_GN`
（`DkMath.NumberTheory.GapFocusing.Support`）。全修飾名・型・証明を維持してLib所有へ移管。
旧モジュールは本モジュールをimportする互換入口である。

隣接二項の線形結合からanchor冪を取り出す。可換環上の可除性であり、素数性も原始性も不要である。

Common divisors of adjacent kernels divide the anchor power in any ring.
-/
theorem dvd_anchor_pow_of_dvd_adjacent_GN
    {R : Type*} [CommRing R] (d : ℕ) (x u q : R)
    (hd : q ∣ GTail d 1 x u) (hs : q ∣ GTail (d + 1) 1 x u) :
    q ∣ u ^ d := by
  rw [GN_succ_left] at hs
  exact (dvd_add_right (hd.mul_left (x + u))).mp hs

/--
[DkMath.Lib] 昇格元: `DkMath.NumberTheory.GapFocusing.dvd_sum_pow_of_dvd_adjacent_GN`
（`DkMath.NumberTheory.GapFocusing.Support`）。全修飾名・型・証明を維持してLib所有へ移管。
旧モジュールは本モジュールをimportする互換入口である。

もう一方の再帰を使うとsum座標の冪が得られる。二つの座標冪を組にして互いに素性へ進む。

Common divisors of adjacent kernels divide the sum-coordinate power.
-/
theorem dvd_sum_pow_of_dvd_adjacent_GN
    {R : Type*} [CommRing R] (d : ℕ) (x u q : R)
    (hd : q ∣ GTail d 1 x u) (hs : q ∣ GTail (d + 1) 1 x u) :
    q ∣ (x + u) ^ d := by
  rw [GN_succ_right] at hs
  exact (dvd_add_right (hd.mul_left u)).mp hs

/--
[DkMath.Lib] 昇格元: `DkMath.NumberTheory.GapFocusing.nat_dvd_powers_of_dvd_adjacent_GN`
（`DkMath.NumberTheory.GapFocusing.Support`）。全修飾名・型・証明を維持してLib所有へ移管。
旧モジュールは本モジュールをimportする互換入口である。

自然数では環の減算を使わず、可除性の加法消去を使う。次数0では共通約数は1しかなく、同じ型のまま扱える。

Natural-number common divisors divide both powers, without subtraction.
-/
theorem nat_dvd_powers_of_dvd_adjacent_GN
    (d x u q : ℕ) (hd : q ∣ GTail d 1 x u)
    (hs : q ∣ GTail (d + 1) 1 x u) :
    q ∣ u ^ d ∧ q ∣ (x + u) ^ d := by
  constructor
  · rw [GN_succ_left] at hs
    exact (Nat.dvd_add_iff_right (hd.mul_left (x + u))).mpr hs
  · rw [GN_succ_right] at hs
    exact (Nat.dvd_add_iff_right (hd.mul_left u)).mpr hs

/--
[DkMath.Lib] 昇格元: `DkMath.NumberTheory.GapFocusing.nat_prime_dvd_coordinates_of_dvd_adjacent_GN`
（`DkMath.NumberTheory.GapFocusing.Support`）。全修飾名・型・証明を維持してLib所有へ移管。
旧モジュールは本モジュールをimportする互換入口である。

共通素数は両座標冪を割り、素数性から底も割る。次数0でも隣接値0と1は共通素数を持たず、仮定が結論を妨げない。

A common prime of adjacent kernels divides both original coordinates.
Degree zero is included: its adjacent values are zero and one, so the
hypothesis cannot hold.
-/
theorem nat_prime_dvd_coordinates_of_dvd_adjacent_GN
    (d x u : ℕ) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ GTail d 1 x u) (hs : p ∣ GTail (d + 1) 1 x u) :
    p ∣ x ∧ p ∣ u := by
  obtain ⟨hu, hv⟩ := nat_dvd_powers_of_dvd_adjacent_GN d x u p hd hs
  have hpu := hp.dvd_of_dvd_pow hu
  have hpv := hp.dvd_of_dvd_pow hv
  exact ⟨(Nat.dvd_add_iff_left hpu).mpr hpv, hpu⟩

/--
[DkMath.Lib] 昇格元: `DkMath.NumberTheory.GapFocusing.nat_coprime_adjacent_GN`
（`DkMath.NumberTheory.GapFocusing.Support`）。全修飾名・型・証明を維持してLib所有へ移管。
旧モジュールは本モジュールをimportする互換入口である。

原始性Coprime x uを保持する。共通素数を座標のgcdへ戻すことで、全次数の隣接GNのgcdが1となる。

Primitive natural coordinate pairs give coprime adjacent kernels at every
degree, including zero.
-/
theorem nat_coprime_adjacent_GN (d x u : ℕ) (h : x.Coprime u) :
    (GTail d 1 x u).Coprime (GTail (d + 1) 1 x u) := by
  apply Nat.coprime_of_dvd'
  intro p hp hd hs
  obtain ⟨hx, hu⟩ := nat_prime_dvd_coordinates_of_dvd_adjacent_GN d x u hp hd hs
  exact (Nat.dvd_gcd hx hu).trans (by rw [h.gcd_eq_one])

/--
[DkMath.Lib] 昇格元: `DkMath.NumberTheory.GapFocusing.nat_one_lt_GN_succ`
（`DkMath.NumberTheory.GapFocusing.Support`）。全修飾名・型・証明を維持してLib所有へ移管。
旧モジュールは本モジュールをimportする互換入口である。

前の次数と両座標の正性を全て保持する。sum座標が2以上なので、その正次数冪だけで後続GNが1より大きくなる。

Positive coordinates and a positive preceding degree make the successor
kernel larger than one.
-/
theorem nat_one_lt_GN_succ (d x u : ℕ)
    (hd : 0 < d) (hx : 0 < x) (hu : 0 < u) :
    1 < GTail (d + 1) 1 x u := by
  rw [GN_succ_right]
  have hv : 1 < (x + u) ^ d :=
    Nat.one_lt_pow (Nat.ne_of_gt hd) (by omega)
  exact lt_of_lt_of_le hv (Nat.le_add_left _ _)

/--
[DkMath.Lib] 昇格元: `DkMath.NumberTheory.GapFocusing.nat_exists_prime_dvd_GN_succ_not_dvd_GN`
（`DkMath.NumberTheory.GapFocusing.Support`）。全修飾名・型・証明を維持してLib所有へ移管。
旧モジュールは本モジュールをimportする互換入口である。

正性から後続項の素因数を選び、原始性から直前項への出現を排除する。全ての過去次数への非出現や付値1は結論しない。

For positive primitive coordinates, every positive-degree transition has
a successor prime absent from its immediate predecessor. No claim is made
about occurrence at other earlier degrees.
-/
theorem nat_exists_prime_dvd_GN_succ_not_dvd_GN (d x u : ℕ)
    (hd : 0 < d) (hx : 0 < x) (hu : 0 < u) (h : x.Coprime u) :
    ∃ p : ℕ, p.Prime ∧ p ∣ GTail (d + 1) 1 x u ∧ ¬p ∣ GTail d 1 x u := by
  obtain ⟨p, hp, hps⟩ :=
    Nat.exists_prime_and_dvd (Nat.ne_of_gt (nat_one_lt_GN_succ d x u hd hx hu))
  have hc := (nat_coprime_adjacent_GN d x u h).coprime_dvd_right hps
  exact ⟨p, hp, hps, hp.coprime_iff_not_dvd.mp hc.symm⟩

/--
[DkMath.Lib] 昇格元: `DkMath.NumberTheory.GapFocusing.dvd_GN_of_dvd_coordinates`
（`DkMath.NumberTheory.GapFocusing.Support`）。全修飾名・型・証明を維持してLib所有へ移管。
旧モジュールは本モジュールをimportする互換入口である。

両座標を割る数は、次数2以上の有限和の全項を割る。次数1のGNは1なので、d+2という下限を保持する。

A common coordinate divisor divides every kernel of degree at least two.
The excluded degree one has kernel one.
-/
theorem dvd_GN_of_dvd_coordinates
    {R : Type*} [CommSemiring R] (d : ℕ) (x u q : R)
    (hx : q ∣ x) (hu : q ∣ u) :
    q ∣ GTail (d + 2) 1 x u := by
  rw [show d + 2 = (d + 1) + 1 by omega, GN_succ_right]
  exact dvd_add (hu.mul_right _) (dvd_pow (dvd_add hx hu) (by omega))

/--
[DkMath.Lib] 昇格元: `DkMath.NumberTheory.GapFocusing.nat_prime_dvd_adjacent_GN_iff`
（`DkMath.NumberTheory.GapFocusing.Support`）。全修飾名・型・証明を維持してLib所有へ移管。
旧モジュールは本モジュールをimportする互換入口である。

次数2以上では、隣接二項の共通素数と両座標の共通素数が一致する。これは素数支持の同値であり、付値の一致を主張しない。

For degrees at least two, adjacent common prime support is precisely the
prime support shared by the coordinates.
-/
theorem nat_prime_dvd_adjacent_GN_iff
    (d x u : ℕ) {p : ℕ} (hp : p.Prime) :
    (p ∣ GTail (d + 2) 1 x u ∧ p ∣ GTail (d + 3) 1 x u) ↔
      p ∣ x ∧ p ∣ u := by
  constructor
  · rintro ⟨hd, hs⟩
    exact nat_prime_dvd_coordinates_of_dvd_adjacent_GN (d + 2) x u hp hd hs
  · rintro ⟨hx, hu⟩
    exact ⟨dvd_GN_of_dvd_coordinates d x u p hx hu,
      dvd_GN_of_dvd_coordinates (d + 1) x u p hx hu⟩

/--
[DkMath.Lib] 昇格元: `DkMath.NumberTheory.GapFocusing.nat_coprime_adjacent_GN_iff`
（`DkMath.NumberTheory.GapFocusing.Support`）。全修飾名・型・証明を維持してLib所有へ移管。
旧モジュールは本モジュールをimportする互換入口である。

次数2以上なら原始性は十分条件だけでなく必要条件になる。次数0・1ではGNの値0・1が現れるため、逆向きへ同じ主張を拡張しない。

For degrees at least two, primitive coordinates are also necessary for
adjacent natural kernels to be coprime.
-/
theorem nat_coprime_adjacent_GN_iff (d x u : ℕ) :
    (GTail (d + 2) 1 x u).Coprime (GTail (d + 3) 1 x u) ↔ x.Coprime u := by
  constructor
  · intro h
    apply Nat.coprime_of_dvd'
    intro p hp hx hu
    have hd := dvd_GN_of_dvd_coordinates d x u p hx hu
    have hs := dvd_GN_of_dvd_coordinates (d + 1) x u p hx hu
    exact (Nat.dvd_gcd hd hs).trans (by rw [h.gcd_eq_one])
  · exact nat_coprime_adjacent_GN (d + 2) x u

/--
[DkMath.Lib] 昇格元: `DkMath.NumberTheory.GapFocusing.isCoprime_adjacent_GN`
（`DkMath.NumberTheory.GapFocusing.Support`）。全修飾名・型・証明を維持してLib所有へ移管。
旧モジュールは本モジュールをimportする互換入口である。

座標のBézout関係を冪へ運び、二つの再帰で隣接GNの線形結合へ戻す。一般可換環のIsCoprimeを保ち、整数gcdの議論に限定しない。

Bézout coprimality of the coordinate pair gives Bézout coprimality of
adjacent kernels over any commutative ring.
-/
theorem isCoprime_adjacent_GN
    {R : Type*} [CommRing R] (d : ℕ) (x u : R) (h : IsCoprime x u) :
    IsCoprime (GTail d 1 x u) (GTail (d + 1) 1 x u) := by
  have hvu : IsCoprime (x + u) u := by
    simpa only [mul_one] using h.add_mul_left_left 1
  have hpowers : IsCoprime (u ^ d) ((x + u) ^ d) := hvu.symm.pow
  obtain ⟨a, b, hab⟩ := hpowers
  refine ⟨-(a * (x + u) + b * u), a + b, ?_⟩
  have hu : u ^ d = GTail (d + 1) 1 x u - (x + u) * GTail d 1 x u := by
    rw [GN_succ_left, add_sub_cancel_left]
  have hv : (x + u) ^ d = GTail (d + 1) 1 x u - u * GTail d 1 x u := by
    rw [GN_succ_right, add_sub_cancel_left]
  rw [hu, hv] at hab
  calc
    -(a * (x + u) + b * u) * GTail d 1 x u +
        (a + b) * GTail (d + 1) 1 x u =
      a * (GTail (d + 1) 1 x u - (x + u) * GTail d 1 x u) +
        b * (GTail (d + 1) 1 x u - u * GTail d 1 x u) := by ring
    _ = 1 := hab

/--
[DkMath.Lib] 昇格元: `DkMath.NumberTheory.GapFocusing.int_gcd_adjacent_GN_eq_one`
（`DkMath.NumberTheory.GapFocusing.Support`）。全修飾名・型・証明を維持してLib所有へ移管。
旧モジュールは本モジュールをimportする互換入口である。

整数のgcdとIsCoprimeの同値による特殊化である。負座標と次数0を許し、正性仮定を追加しない。

The integer gcd version permits negative coordinates and zero degree.
-/
theorem int_gcd_adjacent_GN_eq_one (d : ℕ) (x u : ℤ) (h : Int.gcd x u = 1) :
    Int.gcd (GTail d 1 x u) (GTail (d + 1) 1 x u) = 1 :=
  Int.isCoprime_iff_gcd_eq_one.mp
    (isCoprime_adjacent_GN d x u (Int.isCoprime_iff_gcd_eq_one.mpr h))

end DkMath.NumberTheory.GapFocusing
