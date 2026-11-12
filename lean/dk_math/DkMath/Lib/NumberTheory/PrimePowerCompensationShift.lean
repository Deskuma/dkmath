/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.PrimePowerCompensation
import Mathlib.Data.Nat.GCD.BigOperators

#print "file: DkMath.Lib.NumberTheory.PrimePowerCompensationShift"

/-!
# 正の下側座標へ移した局所補填：サイズ条件を保持する教科書

[DkMath.Lib] GN-LIB-007b。007aのgap `g=p^(p−1)M^p` を保ち、上側座標をx=g+yへ移す。
原始性 `g.Coprime y` の下でLTE、正確な除算、残余Kの支持除去はそのまま成立する。
非完全冪性だけはy=1の場合と異なり、`y^p < x^p−(x−1)^p` を別に要求する。
この条件はx^p−y^pを隣接p乗の間に置くための入力であり、局所付値からは導かない。

有限素数積からyを割る素数を除く。するとq≤Bで、q∣yなら付値0、q∤yなら付値pとなる。
サイズ条件の下で集合外に未完成付値を持つ素数を取り出し、位数pの住所へ接続する。
任意yについてサイズ条件を満たす追加p乗因子を選ぶ工程は007cへ残す。
-/

namespace DkMath.Lib.NumberTheory.PrimePowerCompensation.Shift

open DkMath.Lib.Cosmic DkMath.NumberTheory.GapFocusing
open scoped BigOperators

/-- [DkMath.Lib] 固定したgapへ下側座標yを加えた上側座標。 -/
def base (p M y : ℕ) : ℕ := gap p M + y

/-- [DkMath.Lib] yへ移した余因子の素数pの最初の一層を除いた残余。除算の正確性は後で証明する。 -/
def residual (p M y : ℕ) : ℕ := powerDifferenceCofactor p (base p M y) y / p

/-- [DkMath.Lib] gapの正性による座標の順序。yの正性はまだ不要。 -/
theorem lt_base {p M : ℕ} (hp : p.Prime) (hM : 0 < M) (y : ℕ) : y < base p M y := by
  have := gap_pos hp hM
  unfold base
  omega

/-- [DkMath.Lib] gapとyの原始性は移動後の座標でも保たれる。 -/
theorem base_coprime {p M y : ℕ} (hc : (gap p M).Coprime y) :
    (base p M y).Coprime y := Nat.coprime_add_self_left.mpr hc

/-- [DkMath.Lib] 原始なgapの素因数は移動後の上側座標を割らない。
y=1の場合の「単位との差」を、yとのcoprimeへ置き換える。 -/
theorem not_dvd_base_of_dvd_gap {p M y q : ℕ} (hc : (gap p M).Coprime y)
    (hq : q.Prime) (hg : q ∣ gap p M) : ¬ q ∣ base p M y := by
  have hqy : ¬ q ∣ y := hq.coprime_iff_not_dvd.mp (Nat.Coprime.coprime_dvd_left hg hc)
  intro hb
  exact hqy ((Nat.dvd_add_iff_right hg).mpr hb)

/-- [DkMath.Lib] 奇素数LTEで移動後も余因子のp付値は正確に1。
この算術はサイズ条件を使わず、gapとyの原始性を使う。 -/
theorem cofactor_valuation {p M y : ℕ} (hp : p.Prime) (ho : Odd p) (hM : 0 < M)
    (hc : (gap p M).Coprime y) :
    padicValNat p (powerDifferenceCofactor p (base p M y) y) = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hg : p ∣ base p M y - y := by simpa [base] using prime_dvd_gap (M := M) hp
  rw [padicValNat_powerDifferenceCofactor_of_odd_prime hp ho (lt_base hp hM y) hp.ne_zero hg
    (not_dvd_base_of_dvd_gap hc hp (prime_dvd_gap hp)), padicValNat_self]

/-- [DkMath.Lib] pでの除算は可除性に裏付けられた正確な除去。 -/
theorem prime_mul_residual {p M y : ℕ} (hp : p.Prime) (ho : Odd p) (hM : 0 < M)
    (hc : (gap p M).Coprime y) :
    p * residual p M y = powerDifferenceCofactor p (base p M y) y := by
  have hv := cofactor_valuation hp ho hM hc
  exact Nat.mul_div_cancel' (dvd_of_one_le_padicValNat (by omega))

/-- [DkMath.Lib] 除去後のp付値は0。有限付値の零規約を使って情報を消さない。 -/
theorem residual_valuation {p M y : ℕ} (hp : p.Prime) (ho : Odd p) (hM : 0 < M)
    (hc : (gap p M).Coprime y) : padicValNat p (residual p M y) = 0 := by
  let : Fact p.Prime := ⟨hp⟩
  unfold residual
  rw [padicValNat.div_of_dvd (dvd_of_one_le_padicValNat (by rw [cofactor_valuation hp ho hM hc])),
    cofactor_valuation hp ho hM hc, padicValNat_self]

/-- [DkMath.Lib] 移動後の冪差も(pM)^pと残余の積へ正確に再構成できる。
自然数差はy≤xを先に確保する。 -/
theorem reconstruction {p M y : ℕ} (hp : p.Prime) (ho : Odd p) (hM : 0 < M)
    (hc : (gap p M).Coprime y) :
    base p M y ^ p - y ^ p = (p * M) ^ p * residual p M y := by
  have h := geom_sum₂_mul_of_ge (lt_base hp hM y).le p
  change powerDifferenceCofactor p (base p M y) y * (base p M y - y) =
    base p M y ^ p - y ^ p at h
  have hgap : base p M y - y = gap p M := by simp [base]
  rw [hgap] at h
  rw [← h, ← prime_mul_residual hp ho hM hc]
  have he : p * p ^ (p - 1) = p ^ p := by
    rw [← pow_succ', Nat.sub_add_cancel hp.one_lt.le]
  unfold gap
  rw [mul_pow]
  calc
    p * residual p M y * (p ^ (p - 1) * M ^ p) =
        (p * p ^ (p - 1)) * M ^ p * residual p M y := by ring
    _ = p ^ p * M ^ p * residual p M y := by rw [he]

/-- [DkMath.Lib] 残余は正。サイズ条件を使う前から冪差は非零である。 -/
theorem residual_pos {p M y : ℕ} (hp : p.Prime) (ho : Odd p) (hM : 0 < M)
    (hc : (gap p M).Coprime y) : 0 < residual p M y := by
  have hpow := Nat.pow_lt_pow_left (lt_base hp hM y) hp.ne_zero
  have hr := reconstruction hp ho hM hc
  by_contra hn
  have hz : residual p M y = 0 := by omega
  rw [hz, mul_zero] at hr
  omega

/-- [DkMath.Lib] 原始座標のgap支持を残余から除く。pはLTE、それ以外は余因子gcdで処理する。 -/
theorem not_dvd_residual_of_dvd_gap {p M y q : ℕ}
    (hp : p.Prime) (ho : Odd p) (hM : 0 < M) (hc : (gap p M).Coprime y)
    (hq : q.Prime) (hg : q ∣ gap p M) : ¬ q ∣ residual p M y := by
  intro hr
  by_cases hqp : q = p
  · subst q
    exact (padicValNat_eq_zero_iff hp (Nat.ne_of_gt (residual_pos hp ho hM hc))).mp
      (residual_valuation hp ho hM hc) hr
  · have hdR : q ∣ powerDifferenceCofactor p (base p M y) y := by
      rw [← prime_mul_residual hp ho hM hc]
      exact dvd_mul_of_dvd_right hr p
    have hd : q ∣ Nat.gcd (base p M y - y) (powerDifferenceCofactor p (base p M y) y) :=
      Nat.dvd_gcd (by simpa [base] using hg) hdR
    rw [gcd_gap_powerDifferenceCofactor_eq_gcd_degree hp.one_lt.le
      (lt_base hp hM y).le (base_coprime hc)] at hd
    exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hd.trans (Nat.gcd_dvd_right _ _)))

/-- [DkMath.Lib] gap支持上での局所付値の一般式。任意Mでは値はpの倍数。 -/
theorem local_valuation {p M y q : ℕ} (hp : p.Prime) (ho : Odd p) (hM : 0 < M)
    (hc : (gap p M).Coprime y) (hq : q.Prime) (hg : q ∣ gap p M) :
    padicValNat q (base p M y ^ p - y ^ p) = p * padicValNat q (p * M) := by
  let : Fact q.Prime := ⟨hq⟩
  rw [reconstruction hp ho hM hc, padicValNat.mul
    (pow_ne_zero _ (Nat.mul_ne_zero hp.ne_zero (Nat.ne_of_gt hM)))
    (Nat.ne_of_gt (residual_pos hp ho hM hc)), padicValNat.pow,
    padicValNat.eq_zero_of_not_dvd (not_dvd_residual_of_dvd_gap hp ho hM hc hq hg), add_zero]

/-- [DkMath.Lib] 下側座標yを割る素数は原始冪差を割らない。サイズ条件は使わない。 -/
theorem not_dvd_difference_of_dvd_lower {p M y q : ℕ} (hp : p.Prime) (hM : 0 < M)
    (hc : (gap p M).Coprime y) (hq : q.Prime) (hqy : q ∣ y) :
    ¬ q ∣ base p M y ^ p - y ^ p := by
  intro hd
  have hxpow : q ∣ base p M y ^ p :=
    (Nat.dvd_sub_iff_left (Nat.pow_le_pow_left (lt_base hp hM y).le p)
      (dvd_pow hqy hp.ne_zero)).mp hd
  have hx : q ∣ base p M y := hq.dvd_of_dvd_pow hxpow
  have h1 : q ∣ 1 := by
    have h := Nat.dvd_gcd hx hqy
    simpa only [(base_coprime hc).gcd_eq_one] using h
  exact hq.not_dvd_one h1

/-- [DkMath.Lib] サイズ条件から冪差を連続するp乗の間に置く。
上側の厳密性にはy>0が必要である。下側の不等式こそ次工程で達成すべき入力となる。 -/
theorem difference_between {p M y : ℕ} (hp : p.Prime) (hM : 0 < M) (hy : 0 < y)
    (hsize : y ^ p < base p M y ^ p - (base p M y - 1) ^ p) :
    (base p M y - 1) ^ p < base p M y ^ p - y ^ p ∧
      base p M y ^ p - y ^ p < base p M y ^ p := by
  have h1 := Nat.pow_le_pow_left (Nat.sub_le (base p M y) 1) p
  have h2 := Nat.pow_le_pow_left (lt_base hp hM y).le p
  have h3 := pow_pos hy p
  omega

/-- [DkMath.Lib] サイズ条件を明示した冪差の非完全冪性。局所付値の条件とは独立。 -/
theorem difference_not_pow {p M y : ℕ} (hp : p.Prime) (hM : 0 < M) (hy : 0 < y)
    (hsize : y ^ p < base p M y ^ p - (base p M y - 1) ^ p) :
    ¬ ∃ a : ℕ, a ^ p = base p M y ^ p - y ^ p := by
  obtain ⟨hl, hh⟩ := difference_between hp hM hy hsize
  apply not_pow_of_between_consecutive_powers hl
  have hx : 1 ≤ base p M y := by have := lt_base hp hM y; omega
  simpa only [Nat.sub_add_cancel hx] using hh

/-- [DkMath.Lib] 再構成を通じて非完全冪性をKへ運ぶ。hsizeを省略しない。 -/
theorem residual_not_pow {p M y : ℕ} (hp : p.Prime) (ho : Odd p) (hM : 0 < M)
    (hy : 0 < y) (hc : (gap p M).Coprime y)
    (hsize : y ^ p < base p M y ^ p - (base p M y - 1) ^ p) :
    ¬ ∃ a : ℕ, a ^ p = residual p M y := by
  rintro ⟨a, ha⟩
  apply difference_not_pow hp hM hy hsize
  refine ⟨p * M * a, ?_⟩
  rw [mul_pow, ha, ← reconstruction hp ho hM hc]

/-- [DkMath.Lib] 残余の素因数は両座標を割らず、位数pとp∣q−1の住所を持つ。
原始性で分母yの単元性を証明してから、007aと同じ位数APIを適用する。 -/
theorem residual_prime_address {p M y q : ℕ} (hp : p.Prime) (ho : Odd p) (hM : 0 < M)
    (hc : (gap p M).Coprime y) (hq : q.Prime) (hqr : q ∣ residual p M y) :
    primeOrder q (base p M y) y = p ∧ p ∣ q - 1 := by
  let : Fact q.Prime := ⟨hq⟩
  have hgap : ¬ q ∣ gap p M := fun hg => not_dvd_residual_of_dvd_gap hp ho hM hc hq hg hqr
  have hd : q ∣ base p M y ^ p - y ^ p := by
    rw [reconstruction hp ho hM hc]
    exact dvd_mul_of_dvd_right hqr _
  have hqy : ¬ q ∣ y := fun h => not_dvd_difference_of_dvd_lower hp hM hc hq h hd
  have hb : ¬ (q : ℤ) ∣ (y : ℤ) := by exact_mod_cast hqy
  have hr : primeOrder q (base p M y) y ∣ p :=
    (nat_dvd_pow_sub_pow_iff_primeOrder_dvd (base p M y) y p (lt_base hp hM y).le hqy).mp hd
  have hr1 : primeOrder q (base p M y) y ≠ 1 := by
    intro he
    have hz := (primeOrder_eq_one_iff_dvd_gap (base p M y) y hb).mp he
    have hz' : (q : ℤ) ∣ (gap p M : ℤ) := by
      simpa only [base, Nat.cast_add, add_sub_cancel_right] using hz
    exact hgap (by exact_mod_cast hz')
  have he : primeOrder q (base p M y) y = p := ((Nat.dvd_prime hp).mp hr).resolve_left hr1
  have ha : ¬ q ∣ base p M y := by
    intro hqa
    have hpow : q ∣ base p M y ^ p := dvd_pow hqa hp.ne_zero
    have hyPow : q ∣ y ^ p :=
      (Nat.dvd_sub_iff_right (Nat.pow_le_pow_left (lt_base hp hM y).le p) hpow).mp hd
    exact hqy (hq.dvd_of_dvd_pow hyPow)
  have haZ : ¬ (q : ℤ) ∣ (base p M y : ℤ) := by exact_mod_cast ha
  exact ⟨he, he ▸ primeOrder_dvd_prime_sub_one haZ hb⟩


/-- [DkMath.Lib] 下側座標の素因数はKも割らない。正確な再構成から冪差へ戻して除外する。 -/
theorem not_dvd_residual_of_dvd_lower {p M y q : ℕ} (hp : p.Prime) (ho : Odd p)
    (hM : 0 < M) (hc : (gap p M).Coprime y) (hq : q.Prime) (hqy : q ∣ y) :
    ¬ q ∣ residual p M y := by
  intro hqr
  apply not_dvd_difference_of_dvd_lower hp hM hc hq hqy
  rw [reconstruction hp ho hM hc]
  exact dvd_mul_of_dvd_right hqr _

/-- [DkMath.Lib] pMとyが互いに素なら、同じ素数支持を持つgapとも互いに素。
後続の追加p乗因子の選択にも使える、原始性を保つ一般核である。 -/
theorem gap_coprime_of_mul_coprime {p M y : ℕ} (hc : (p * M).Coprime y) :
    (gap p M).Coprime y := by
  have h := Nat.coprime_mul_iff_left.mp hc
  exact Nat.coprime_mul_iff_left.mpr ⟨h.1.pow_left _, h.2.pow_left _⟩

/-- [DkMath.Lib] yを割る素数も除外した標準制御積。 -/
def primeProduct (p B y : ℕ) : ℕ :=
  ∏ q ∈ (Finset.range (B + 1)).filter (fun q => q.Prime ∧ q ≠ p ∧ ¬ q ∣ y), q

/-- [DkMath.Lib] 制御積は空積を含めて正。 -/
theorem primeProduct_pos (p B y : ℕ) : 0 < primeProduct p B y := by
  apply Finset.prod_pos
  intro q hq
  exact (Finset.mem_filter.mp hq).2.1.pos

/-- [DkMath.Lib] 積の全ての因子からyの素因数を除くことで、yとの原始性を構成する。 -/
theorem primeProduct_coprime (p B y : ℕ) : (primeProduct p B y).Coprime y := by
  apply Nat.coprime_prod_left_iff.mpr
  intro q hq
  have h := (Finset.mem_filter.mp hq).2
  exact h.1.coprime_iff_not_dvd.mpr h.2.2

/-- [DkMath.Lib] p∤yを加えるとpMおよびgapもyと互いに素となる。 -/
theorem standard_gap_coprime {p B y : ℕ} (hp : p.Prime) (hpy : ¬ p ∣ y) :
    (gap p (primeProduct p B y)).Coprime y := by
  apply gap_coprime_of_mul_coprime
  exact Nat.coprime_mul_iff_left.mpr
    ⟨hp.coprime_iff_not_dvd.mpr hpy, primeProduct_coprime p B y⟩

/-- [DkMath.Lib] 指数素数pは標準制御積に含まれない。 -/
theorem prime_not_dvd_primeProduct {p B y : ℕ} (hp : p.Prime) :
    ¬ p ∣ primeProduct p B y := by
  apply hp.prime.not_dvd_finsetProd
  intro q hq hd
  have h := (Finset.mem_filter.mp hq).2
  exact h.2.1 ((Nat.prime_dvd_prime_iff_eq hp h.1).mp hd).symm

/-- [DkMath.Lib] q≤B、q∤yなら、pMのq付値は正確に1。
q=pの分岐と、積の一因子を抜く分岐を分け、平方自由性を具体的に証明する。 -/
theorem small_prime_product_valuation {p B y q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hB : q ≤ B) (hqy : ¬ q ∣ y) :
    padicValNat q (p * primeProduct p B y) = 1 := by
  let : Fact q.Prime := ⟨hq⟩
  rw [padicValNat.mul hp.ne_zero (Nat.ne_of_gt (primeProduct_pos p B y))]
  by_cases hqp : q = p
  · subst q
    rw [padicValNat_self, padicValNat.eq_zero_of_not_dvd (prime_not_dvd_primeProduct hp), add_zero]
  · have hnotp : ¬ q ∣ p := fun h => hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp h)
    rw [padicValNat.eq_zero_of_not_dvd hnotp, zero_add]
    let S := (Finset.range (B + 1)).filter (fun r => r.Prime ∧ r ≠ p ∧ ¬ r ∣ y)
    have hmem : q ∈ S := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), hq, hqp, hqy⟩
    have hrest : ¬ q ∣ ∏ r ∈ S.erase q, r := by
      apply hq.prime.not_dvd_finsetProd
      intro r hr hd
      have hne := (Finset.mem_erase.mp hr).1
      have hrp := (Finset.mem_filter.mp (Finset.mem_erase.mp hr).2).2.1
      exact hne ((Nat.prime_dvd_prime_iff_eq hq hrp).mp hd).symm
    have hnrest : (∏ r ∈ S.erase q, r) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro r hr
      exact ((Finset.mem_filter.mp (Finset.mem_erase.mp hr).2).2.1).ne_zero
    change padicValNat q (∏ r ∈ S, r) = 1
    rw [← Finset.mul_prod_erase S (fun r : ℕ => r) hmem,
      padicValNat.mul hq.ne_zero hnrest, padicValNat_self,
      padicValNat.eq_zero_of_not_dvd hrest, add_zero]

/-- [DkMath.Lib] 上限内でyを割らない素数は、pを含めgap支持へ入る。 -/
theorem small_prime_dvd_gap {p B y q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hB : q ≤ B) (hqy : ¬ q ∣ y) : q ∣ gap p (primeProduct p B y) := by
  by_cases hqp : q = p
  · subst q; exact prime_dvd_gap hp
  · have hd : q ∣ primeProduct p B y := Finset.dvd_prod_of_mem (fun q : ℕ => q)
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hq, hqp, hqy⟩)
    exact dvd_mul_of_dvd_right (dvd_pow hd hp.ne_zero) _

/-- [DkMath.Lib] 小素数の正確な二分法。q∣yなら0、それ以外ならp。
サイズ条件を要求しない局所算術であり、q=2の分岐も原始性とgcdで扱う。 -/
theorem small_prime_valuation_exact {p B y q : ℕ} (hp : p.Prime) (ho : Odd p)
    (hpy : ¬ p ∣ y) (hq : q.Prime) (hB : q ≤ B) :
    padicValNat q (base p (primeProduct p B y) y ^ p - y ^ p) = if q ∣ y then 0 else p := by
  have hc := standard_gap_coprime (B := B) hp hpy
  split_ifs with hqy
  · exact padicValNat.eq_zero_of_not_dvd
      (not_dvd_difference_of_dvd_lower hp (primeProduct_pos p B y) hc hq hqy)
  · rw [local_valuation hp ho (primeProduct_pos p B y) hc hq (small_prime_dvd_gap hp hq hB hqy),
      small_prime_product_valuation hp hq hB hqy, mul_one]

/-- [DkMath.Lib] yを割る枝も含め、全ての小素数で付値はpの倍数になる。 -/
theorem small_prime_local_completion {p B y q : ℕ} (hp : p.Prime) (ho : Odd p)
    (hpy : ¬ p ∣ y) (hq : q.Prime) (hB : q ≤ B) :
    p ∣ padicValNat q (base p (primeProduct p B y) y ^ p - y ^ p) := by
  rw [small_prime_valuation_exact hp ho hpy hq hB]
  split_ifs <;> simp

/-- [DkMath.Lib] 残余の素因数は全て上限Bを超える。非完全冪性やサイズ条件はまだ不要。 -/
theorem not_dvd_residual_of_small_prime {p B y q : ℕ} (hp : p.Prime) (ho : Odd p)
    (hpy : ¬ p ∣ y) (hq : q.Prime) (hB : q ≤ B) :
    ¬ q ∣ residual p (primeProduct p B y) y := by
  have hc := standard_gap_coprime (B := B) hp hpy
  by_cases hqy : q ∣ y
  · exact not_dvd_residual_of_dvd_lower hp ho (primeProduct_pos p B y) hc hq hqy
  · exact not_dvd_residual_of_dvd_gap hp ho (primeProduct_pos p B y) hc hq
      (small_prime_dvd_gap hp hq hB hqy)

/-- [DkMath.Lib] サイズ条件の下でのみ、上限外の未完成付値を持つ素数の存在を得る。
y>0とp∤yを保持し、位数pとp∣q−1も同時に返す。 -/
theorem exists_prime_escape_with_address {p B y : ℕ} (hp : p.Prime) (ho : Odd p)
    (hy : 0 < y) (hpy : ¬ p ∣ y)
    (hsize : y ^ p < base p (primeProduct p B y) y ^ p -
      (base p (primeProduct p B y) y - 1) ^ p) :
    ∃ q, q.Prime ∧ B < q ∧ q ∣ residual p (primeProduct p B y) y ∧
      ¬ p ∣ padicValNat q (residual p (primeProduct p B y) y) ∧
      primeOrder q (base p (primeProduct p B y) y) y = p ∧ p ∣ q - 1 := by
  have hc := standard_gap_coprime (B := B) hp hpy
  have hM := primeProduct_pos p B y
  obtain ⟨q, hq, hqr, hv⟩ := exists_prime_padicValNat_not_dvd
    (Nat.ne_of_gt (residual_pos hp ho hM hc)) (residual_not_pow hp ho hM hy hc hsize)
  have hB : B < q := by
    by_contra hn
    exact not_dvd_residual_of_small_prime hp ho hpy hq (by omega) hqr
  obtain ⟨hr, ha⟩ := residual_prime_address hp ho hM hc hq hqr
  exact ⟨q, hq, hB, hqr, hv, hr, ha⟩

/-- [DkMath.Lib] 任意の有限集合での局所完済と、サイズ条件付きの集合外脱出。
集合の最大値を使うが、集合の要素が全て素数だとは仮定しない。 -/
theorem finite_set_compensation_and_escape {p y : ℕ} (hp : p.Prime) (ho : Odd p)
    (hy : 0 < y) (hpy : ¬ p ∣ y) (S : Finset ℕ)
    (hsize : let M := primeProduct p (S.sup id) y
      y ^ p < base p M y ^ p - (base p M y - 1) ^ p) :
    let M := primeProduct p (S.sup id) y
    (∀ q ∈ S, q.Prime → padicValNat q (base p M y ^ p - y ^ p) = if q ∣ y then 0 else p) ∧
      ∃ q, q.Prime ∧ q ∉ S ∧ q ∣ residual p M y ∧
        ¬ p ∣ padicValNat q (residual p M y) ∧ primeOrder q (base p M y) y = p ∧ p ∣ q - 1 := by
  dsimp only at hsize ⊢
  constructor
  · intro q hq hprime
    exact small_prime_valuation_exact hp ho hpy hprime (Finset.le_sup (f := id) hq)
  · obtain ⟨q, hq, hB, hqr, hv, hr, ha⟩ := exists_prime_escape_with_address hp ho hy hpy hsize
    exact ⟨q, hq, fun hmem => (not_le_of_gt hB) (Finset.le_sup (f := id) hmem),
      hqr, hv, hr, ha⟩

/-- [DkMath.Lib] 下側座標1の上側座標は007aの定義と一致する。 -/
theorem base_one (p M : ℕ) : base p M 1 = PrimePowerCompensation.base p M := rfl

/-- [DkMath.Lib] 下側座標1の残余は007aの定義と一致する。 -/
theorem residual_one (p M : ℕ) : residual p M 1 = PrimePowerCompensation.residual p M := rfl

/-- [DkMath.Lib] y=1では除外する追加素数がなく、007aの制御積へ戻る。 -/
theorem primeProduct_one (p B : ℕ) : primeProduct p B 1 = PrimePowerCompensation.primeProduct p B := by
  unfold primeProduct PrimePowerCompensation.primeProduct
  apply Finset.prod_congr ?_ (fun _ _ => rfl)
  ext q
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hr, hq, hne, _⟩
    exact ⟨hr, hq, hne⟩
  · rintro ⟨hr, hq, hne⟩
    exact ⟨hr, hq, hne, hq.not_dvd_one⟩

/-! ## 翻訳を追うための例

y=2の残余49=7²は、未完成付値が1とは限らないことを示す。
局所算術はサイズ条件に依存せず、非完全冪性と脱出だけが依存する。
-/
example : primeProduct 3 3 2 = 1 ∧ base 3 1 2 = 11 ∧ residual 3 1 2 = 49 := by decide

example : padicValNat 2 (base 3 (primeProduct 3 3 2) 2 ^ 3 - 2 ^ 3) = 0 := by
  rw [small_prime_valuation_exact (by decide) (by decide) (by decide) (by decide) (by decide)]
  decide

example : padicValNat 3 (base 3 (primeProduct 3 3 2) 2 ^ 3 - 2 ^ 3) = 3 := by
  rw [small_prime_valuation_exact (by decide) (by decide) (by decide) (by decide) (by decide)]
  decide

example : padicValNat 7 (residual 3 1 2) = 2 := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  change padicValNat 7 (7 ^ 2) = 2
  exact padicValNat.prime_pow 2

example : primeOrder 7 (base 3 1 2) 2 = 3 ∧ 3 ∣ 7 - 1 :=
  residual_prime_address (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

example : ¬ ∃ a : ℕ, a ^ 3 = residual 3 1 2 :=
  residual_not_pow (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

example : ∃ q, q.Prime ∧ 3 < q ∧ q ∣ residual 3 (primeProduct 3 3 2) 2 ∧
    ¬ 3 ∣ padicValNat q (residual 3 (primeProduct 3 3 2) 2) ∧
    primeOrder q (base 3 (primeProduct 3 3 2) 2) 2 = 3 ∧ 3 ∣ q - 1 :=
  exists_prime_escape_with_address (by decide) (by decide) (by decide) (by decide) (by decide)

example : primeProduct 3 5 5 = 2 ∧ base 3 (primeProduct 3 5 5) 5 = 77 := by decide

-- 標準積が原始性を保っても、サイズ条件は自動的には成立しない。
example : (gap 3 (primeProduct 3 3 1001)).Coprime 1001 ∧
    ¬ (1001 ^ 3 < base 3 (primeProduct 3 3 1001) 1001 ^ 3 -
      (base 3 (primeProduct 3 3 1001) 1001 - 1) ^ 3) := by decide

-- p∤yを落とすと標準構成の原始性が壊れる。
example : ¬ (gap 3 (primeProduct 3 3 3)).Coprime 3 := by decide

example (p B : ℕ) : primeProduct p B 1 = PrimePowerCompensation.primeProduct p B :=
  primeProduct_one p B

end DkMath.Lib.NumberTheory.PrimePowerCompensation.Shift
