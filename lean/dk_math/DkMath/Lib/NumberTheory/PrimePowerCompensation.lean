/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.PerfectPowerValuation
import DkMath.Lib.NumberTheory.PowerDifferenceCofactorValuation
import DkMath.Lib.NumberTheory.PowerDifferenceCofactorGcd
import DkMath.Lib.NumberTheory.PowerDifferenceCofactorPrimeAddress
import Mathlib.Algebra.BigOperators.Associated

#print "file: DkMath.Lib.NumberTheory.PrimePowerCompensation"

/-!
# 有限素数の局所補填と集合外への脱出：y=1の構成

[DkMath.Lib] GN-LIB-007a。奇素数p、正のMに対し
`g = p^(p-1) M^p`、`x = g+1`、`K = R_p(x,1)/p` とおく。
LTEからv_p(R_p)=1、gapのgcdからKはgの全素因数を避ける。
したがって `x^p-1=(pM)^p K` はgの支持上で局所的にp乗として完成する。

一方x^p−1は連続するp乗の間にあり、Kもp乗でない。
素因数分解からKには付値がpの倍数でない素数が存在し、その素数は制御集合の外へ出る。
これは選んだ構成の定理であり、任意のFLT反例からの降下写像ではない。
一般のyでは別のサイズ条件が必要になるため、この教材はy=1を固定する。
-/

namespace DkMath.Lib.NumberTheory.PrimePowerCompensation

open DkMath.Lib.Cosmic DkMath.NumberTheory.GapFocusing
open scoped BigOperators

/-- [DkMath.Lib] gapのp付値の最初のp−1層と、Mのp乗による追加補填。 -/
def gap (p M : ℕ) : ℕ := p ^ (p - 1) * M ^ p

/-- [DkMath.Lib] 下側座標1に対する上側座標。 -/
def base (p M : ℕ) : ℕ := gap p M + 1

/-- [DkMath.Lib] 余因子のpの最初の一層を除いた残余。可除性は以下で証明する。 -/
def residual (p M : ℕ) : ℕ := powerDifferenceCofactor p (base p M) 1 / p

/-- [DkMath.Lib] 正のMと素数pならgapが正となり、上側座標は1より大きい。 -/
theorem gap_pos {p M : ℕ} (hp : p.Prime) (hM : 0 < M) : 0 < gap p M :=
  Nat.mul_pos (pow_pos hp.pos _) (pow_pos hM _)

/-- [DkMath.Lib] 指数素数pはgapの支持に入る。 -/
theorem prime_dvd_gap {p M : ℕ} (hp : p.Prime) : p ∣ gap p M :=
  dvd_mul_of_dvd_left (dvd_pow_self p (by have := hp.two_le; omega)) _

/-- [DkMath.Lib] gapを割る素数はbaseを割らない。差は単位1である。 -/
theorem not_dvd_base_of_dvd_gap {p M q : ℕ} (hq : q.Prime) (hg : q ∣ gap p M) :
    ¬ q ∣ base p M := by
  intro hb
  exact hq.not_dvd_one ((Nat.dvd_add_iff_right hg).mpr hb)

/-- [DkMath.Lib] 奇素数LTEでv_p(R_p)=1。Mにpが含まれていても成立する。 -/
theorem cofactor_valuation {p M : ℕ} (hp : p.Prime) (ho : Odd p) (hM : 0 < M) :
    padicValNat p (powerDifferenceCofactor p (base p M) 1) = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hx : 1 < base p M := by have := gap_pos hp hM; unfold base; omega
  have hgap : p ∣ base p M - 1 := by simpa [base] using prime_dvd_gap (M := M) hp
  rw [padicValNat_powerDifferenceCofactor_of_odd_prime hp ho hx hp.ne_zero hgap
    (not_dvd_base_of_dvd_gap hp (prime_dvd_gap hp)), padicValNat_self]

/-- [DkMath.Lib] pでの除算は正確であり、切り捨てを含まない。 -/
theorem prime_mul_residual {p M : ℕ} (hp : p.Prime) (ho : Odd p) (hM : 0 < M) :
    p * residual p M = powerDifferenceCofactor p (base p M) 1 := by
  have hv := cofactor_valuation hp ho hM
  have hd : p ∣ powerDifferenceCofactor p (base p M) 1 :=
    dvd_of_one_le_padicValNat (by omega)
  exact Nat.mul_div_cancel' hd

/-- [DkMath.Lib] 残余のp付値は0。除算前の付値1を厳密に除去する。 -/
theorem residual_valuation {p M : ℕ} (hp : p.Prime) (ho : Odd p) (hM : 0 < M) :
    padicValNat p (residual p M) = 0 := by
  let : Fact p.Prime := ⟨hp⟩
  unfold residual
  rw [padicValNat.div_of_dvd (dvd_of_one_le_padicValNat (by rw [cofactor_valuation hp ho hM])),
    cofactor_valuation hp ho hM, padicValNat_self]

/-- [DkMath.Lib] 乗法的補填の正確な再構成。加法的な完成不足D_nとは別の量である。 -/
theorem reconstruction {p M : ℕ} (hp : p.Prime) (ho : Odd p) (hM : 0 < M) :
    base p M ^ p - 1 = (p * M) ^ p * residual p M := by
  have hx : 1 ≤ base p M := by simp [base]
  have h := geom_sum₂_mul_of_ge hx p
  change powerDifferenceCofactor p (base p M) 1 * (base p M - 1) =
    base p M ^ p - 1 ^ p at h
  rw [one_pow, base, Nat.add_sub_cancel] at h
  calc
    base p M ^ p - 1 = powerDifferenceCofactor p (base p M) 1 * gap p M := by
      simpa only [base] using h.symm
    _ = (p * residual p M) * (p ^ (p - 1) * M ^ p) := by
      rw [prime_mul_residual hp ho hM]; rfl
    _ = (p * M) ^ p * residual p M := by
      have he : p * p ^ (p - 1) = p ^ p := by
        rw [← pow_succ', Nat.sub_add_cancel hp.one_lt.le]
      rw [mul_pow]
      calc
        (p * residual p M) * (p ^ (p - 1) * M ^ p) =
            (p * p ^ (p - 1)) * M ^ p * residual p M := by ring
        _ = p ^ p * M ^ p * residual p M := by rw [he]

/-- [DkMath.Lib] 残余は正。有限付値の乗法性の前に非零性を確保する。 -/
theorem residual_pos {p M : ℕ} (hp : p.Prime) (ho : Odd p) (hM : 0 < M) :
    0 < residual p M := by
  have hx : 1 < base p M := by have := gap_pos hp hM; unfold base; omega
  have hpow : 1 < base p M ^ p := Nat.one_lt_pow hp.ne_zero hx
  have hr := reconstruction hp ho hM
  by_contra hn
  have hz : residual p M = 0 := by omega
  rw [hz, mul_zero] at hr
  omega

/-- [DkMath.Lib] gapの素数支持を残余から完全に除く。指数素数pはLTE、他はgcd還元で除く。 -/
theorem not_dvd_residual_of_dvd_gap {p M q : ℕ}
    (hp : p.Prime) (ho : Odd p) (hM : 0 < M) (hq : q.Prime) (hg : q ∣ gap p M) :
    ¬ q ∣ residual p M := by
  intro hr
  by_cases hqp : q = p
  · subst q
    exact (padicValNat_eq_zero_iff hp (Nat.ne_of_gt (residual_pos hp ho hM))).mp
      (residual_valuation hp ho hM) hr
  · have hdR : q ∣ powerDifferenceCofactor p (base p M) 1 := by
      rw [← prime_mul_residual hp ho hM]
      exact dvd_mul_of_dvd_right hr p
    have hd : q ∣ Nat.gcd (base p M - 1) (powerDifferenceCofactor p (base p M) 1) :=
      Nat.dvd_gcd (by simpa [base] using hg) hdR
    rw [gcd_gap_powerDifferenceCofactor_eq_gcd_degree hp.one_lt.le
      (by simp [base]) (by simp)] at hd
    have hqp' : q ∣ p := hd.trans (Nat.gcd_dvd_right _ _)
    exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp hqp')

/-- [DkMath.Lib] gapの支持では付値がpの倍数となる。Mの平方自由性は要求しないので、
値そのものがpに等しいとは限らない。pを含むMでもこの正確な式が成立する。 -/
theorem local_valuation {p M q : ℕ} (hp : p.Prime) (ho : Odd p) (hM : 0 < M)
    (hq : q.Prime) (hg : q ∣ gap p M) :
    padicValNat q (base p M ^ p - 1) = p * padicValNat q (p * M) := by
  let : Fact q.Prime := ⟨hq⟩
  rw [reconstruction hp ho hM, padicValNat.mul
    (pow_ne_zero _ (Nat.mul_ne_zero hp.ne_zero (Nat.ne_of_gt hM)))
    (Nat.ne_of_gt (residual_pos hp ho hM)), padicValNat.pow,
    padicValNat.eq_zero_of_not_dvd (not_dvd_residual_of_dvd_gap hp ho hM hq hg), add_zero]

/-- [DkMath.Lib] 隣接p乗の間隔によって、選んだ構成の残余はp乗でないと分かる。 -/
theorem residual_not_pow {p M : ℕ} (hp : p.Prime) (ho : Odd p) (hM : 0 < M) :
    ¬ ∃ a : ℕ, a ^ p = residual p M := by
  rintro ⟨a, ha⟩
  have hx : 1 < base p M := by have := gap_pos hp hM; unfold base; omega
  apply not_pow_pow_sub_one hx hp.two_le
  refine ⟨p * M * a, ?_⟩
  rw [mul_pow, ha, ← reconstruction hp ho hM]

/-- [DkMath.Lib] 残余の素因数の乗法位数はpであり、q≡1 mod pの住所を持つ。
付値の深さとは独立の結論である。有限集合を選ぶ前の任意の正のMで成立する。 -/
theorem residual_prime_address {p M q : ℕ} (hp : p.Prime) (ho : Odd p)
    (hM : 0 < M) (hq : q.Prime) (hqr : q ∣ residual p M) :
    primeOrder q (base p M) 1 = p ∧ p ∣ q - 1 := by
  let : Fact q.Prime := ⟨hq⟩
  have hx : 1 < base p M := by have := gap_pos hp hM; unfold base; omega
  have hgap : ¬ q ∣ gap p M := fun hg =>
    not_dvd_residual_of_dvd_gap hp ho hM hq hg hqr
  have hd : q ∣ base p M ^ p - 1 := by
    rw [reconstruction hp ho hM]
    exact dvd_mul_of_dvd_right hqr _
  have hd' : q ∣ base p M ^ p - 1 ^ p := by simpa using hd
  have hb : ¬ (q : ℤ) ∣ (1 : ℤ) := by
    exact_mod_cast hq.not_dvd_one
  have hr : primeOrder q (base p M) 1 ∣ p :=
    (nat_dvd_pow_sub_pow_iff_primeOrder_dvd (base p M) 1 p hx.le
      hq.not_dvd_one).mp hd'
  have hr1 : primeOrder q (base p M) 1 ≠ 1 := by
    intro he
    have hz := (primeOrder_eq_one_iff_dvd_gap (base p M) 1 hb).mp he
    have hz' : (q : ℤ) ∣ (gap p M : ℤ) := by
      simpa only [base, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hz
    exact hgap (by exact_mod_cast hz')
  have he : primeOrder q (base p M) 1 = p := ((Nat.dvd_prime hp).mp hr).resolve_left hr1
  have ha : ¬ q ∣ base p M := by
    intro hqa
    have hpow : q ∣ base p M ^ p := dvd_pow hqa hp.ne_zero
    exact hq.not_dvd_one ((Nat.dvd_sub_iff_right (Nat.one_le_pow p _ hx.le) hpow).mp hd)
  have haZ : ¬ (q : ℤ) ∣ (base p M : ℤ) := by exact_mod_cast ha
  exact ⟨he, he ▸ primeOrder_dvd_prime_sub_one haZ hb⟩

/-- [DkMath.Lib] 上限Bまでの素数のうち指数素数pを除いた有限積。 -/
def primeProduct (p B : ℕ) : ℕ :=
  ∏ q ∈ (Finset.range (B + 1)).filter (fun q => q.Prime ∧ q ≠ p), q

/-- [DkMath.Lib] 制御積は空積1も許す正の数である。 -/
theorem primeProduct_pos (p B : ℕ) : 0 < primeProduct p B := by
  apply Finset.prod_pos
  intro q hq
  exact (Finset.mem_filter.mp hq).2.1.pos

/-- [DkMath.Lib] 制御積はpを除く。各因子はpと異なる素数である。 -/
theorem prime_not_dvd_primeProduct {p B : ℕ} (hp : p.Prime) :
    ¬ p ∣ primeProduct p B := by
  apply hp.prime.not_dvd_finsetProd
  intro q hq hd
  have h := (Finset.mem_filter.mp hq).2
  exact h.2 ((Nat.prime_dvd_prime_iff_eq hp h.1).mp hd).symm

/-- [DkMath.Lib] 小素数qはpMに正確に一度現れる。pの場合は除外積、他は
有限集合の一因子と残りの積へ分ける。有限集合の重複除去が付値1を保証する。 -/
theorem small_prime_product_valuation {p B q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hB : q ≤ B) : padicValNat q (p * primeProduct p B) = 1 := by
  let : Fact q.Prime := ⟨hq⟩
  rw [padicValNat.mul hp.ne_zero (Nat.ne_of_gt (primeProduct_pos p B))]
  by_cases hqp : q = p
  · subst q
    rw [padicValNat_self, padicValNat.eq_zero_of_not_dvd (prime_not_dvd_primeProduct hp), add_zero]
  · have hnotp : ¬ q ∣ p := fun h => hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp h)
    rw [padicValNat.eq_zero_of_not_dvd hnotp, zero_add]
    let S := (Finset.range (B + 1)).filter (fun r => r.Prime ∧ r ≠ p)
    have hmem : q ∈ S := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), hq, hqp⟩
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

/-- [DkMath.Lib] 上限以下の全素数は、p自身を含め構成したgapを割る。 -/
theorem small_prime_dvd_gap {p B q : ℕ} (hp : p.Prime) (hq : q.Prime) (hB : q ≤ B) :
    q ∣ gap p (primeProduct p B) := by
  by_cases hqp : q = p
  · subst q; exact prime_dvd_gap hp
  · have hd : q ∣ primeProduct p B := Finset.dvd_prod_of_mem (fun q : ℕ => q)
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hq, hqp⟩)
    exact dvd_mul_of_dvd_right (dvd_pow hd hp.ne_zero) _

/-- [DkMath.Lib] 有限上限内での局所完済。各付値はpの倍数となる。
上限Bに対する仮定B≥pは不要で、pは構成上常に補填されている。 -/
theorem small_prime_local_completion {p B q : ℕ} (hp : p.Prime) (ho : Odd p)
    (hq : q.Prime) (hB : q ≤ B) :
    p ∣ padicValNat q (base p (primeProduct p B) ^ p - 1) := by
  rw [local_valuation hp ho (primeProduct_pos p B) hq (small_prime_dvd_gap hp hq hB)]
  exact dvd_mul_right p _

/-- [DkMath.Lib] 標準の平方自由な制御積では、上限以下の各素数の付値は正確にp。
より一般のMに対する「pの倍数」という結論と区別する。 -/
theorem small_prime_valuation_exact {p B q : ℕ} (hp : p.Prime) (ho : Odd p)
    (hq : q.Prime) (hB : q ≤ B) :
    padicValNat q (base p (primeProduct p B) ^ p - 1) = p := by
  rw [local_valuation hp ho (primeProduct_pos p B) hq (small_prime_dvd_gap hp hq hB),
    small_prime_product_valuation hp hq hB, mul_one]

/-- [DkMath.Lib] 任意の有限上限の外に、未完成付値を持つ素因数が存在する。
非完全冪性は先に隣接冪の間隔から証明済みである。原始素因数の付値1は要求しない。 -/
theorem exists_prime_escape {p B : ℕ} (hp : p.Prime) (ho : Odd p) :
    ∃ q, q.Prime ∧ B < q ∧ q ∣ residual p (primeProduct p B) ∧
      ¬ p ∣ padicValNat q (residual p (primeProduct p B)) := by
  have hM := primeProduct_pos p B
  obtain ⟨q, hq, hqr, hv⟩ := exists_prime_padicValNat_not_dvd
    (Nat.ne_of_gt (residual_pos hp ho hM)) (residual_not_pow hp ho hM)
  refine ⟨q, hq, ?_, hqr, hv⟩
  by_contra hB
  exact not_dvd_residual_of_dvd_gap hp ho hM hq
    (small_prime_dvd_gap hp hq (by omega)) hqr

/-- [DkMath.Lib] 付値障害と乗法位数の住所を一つの存在命題にまとめる。
大素数の存在を仮定せず、有限分解と非完全冪性から構成する。 -/
theorem exists_prime_escape_with_address {p B : ℕ} (hp : p.Prime) (ho : Odd p) :
    ∃ q, q.Prime ∧ B < q ∧ q ∣ residual p (primeProduct p B) ∧
      ¬ p ∣ padicValNat q (residual p (primeProduct p B)) ∧
      primeOrder q (base p (primeProduct p B)) 1 = p ∧ p ∣ q - 1 := by
  obtain ⟨q, hq, hB, hqr, hv⟩ := exists_prime_escape (B := B) hp ho
  obtain ⟨hr, haddr⟩ := residual_prime_address hp ho (primeProduct_pos p B) hq hqr
  exact ⟨q, hq, hB, hqr, hv, hr, haddr⟩

/-- [DkMath.Lib] 有限上限ではなく任意の有限集合Sに対する同時構成。
Sが素数だけからなる仮定は不要で、S内の素数について局所完済する。
集合外の素数は未完成付値と位数pの住所を併せ持つ。 -/
theorem finite_set_compensation_and_escape {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (S : Finset ℕ) :
    let M := primeProduct p (S.sup id)
    (∀ q ∈ S, q.Prime → padicValNat q (base p M ^ p - 1) = p) ∧
      ∃ q, q.Prime ∧ q ∉ S ∧ q ∣ residual p M ∧
        ¬ p ∣ padicValNat q (residual p M) ∧ primeOrder q (base p M) 1 = p ∧ p ∣ q - 1 := by
  dsimp only
  constructor
  · intro q hq hprime
    exact small_prime_valuation_exact hp ho hprime (Finset.le_sup (f := id) hq)
  · obtain ⟨q, hq, hB, hqr, hv, hr, ha⟩ :=
      exists_prime_escape_with_address (B := S.sup id) hp ho
    exact ⟨q, hq, fun hmem => (not_le_of_gt hB) (Finset.le_sup (f := id) hmem),
      hqr, hv, hr, ha⟩

/-! ## 境界と具体例
空積、最小の奇素数、Mがpを含む場合、p=2の除外を確認する。
-/
example : primeProduct 3 1 = 1 := by decide
example : gap 3 1 = 9 ∧ base 3 1 = 10 ∧ residual 3 1 = 37 := by decide
example : primeProduct 3 3 = 2 ∧ base 3 (primeProduct 3 3) = 73 ∧
    residual 3 (primeProduct 3 3) = 1801 := by decide
example (B : ℕ) : ∃ q, q.Prime ∧ B < q ∧ q ∣ residual 3 (primeProduct 3 B) ∧
    ¬ 3 ∣ padicValNat q (residual 3 (primeProduct 3 B)) :=
  exists_prime_escape (by decide) (by decide)
example : padicValNat 3 (base 3 3 ^ 3 - 1) = 6 := by
  rw [local_valuation (by decide) (by decide) (by decide) (by decide) (prime_dvd_gap (by decide))]
  change 3 * padicValNat 3 (3 ^ 2) = 6
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [padicValNat.prime_pow]
example : powerDifferenceCofactor 2 (base 2 1) 1 = 4 := by decide
-- 2進ではR_2(3,1)=4なのでpの一層だけを除いてもgap支持が残る。
example : 2 ∣ residual 2 1 := by decide
-- y>1への拡張にはサイズ条件が必要。資料の無条件な一般化を使わない。
example : ¬ (1001 ^ 3 < 1073 ^ 3 - 1072 ^ 3) := by decide
example : (residual 3 1 : ℕ) ≠ 0 := Nat.ne_of_gt (residual_pos (by decide) (by decide) (by decide))

end DkMath.Lib.NumberTheory.PrimePowerCompensation
