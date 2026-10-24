/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.PrimePowerCompensationShift

#print "file: DkMath.Lib.NumberTheory.PrimePowerCompensationLift"

/-!
# 局所付値を保ってサイズ条件を達成する追加因子

[DkMath.Lib] GN-LIB-007c。007bの制御積をM₀とし、C=pM₀y、T=C y^p+1、M=M₀Tとおく。
TはCと互いに素なので、yとの原始性と制御小素数の正確な付値を保つ。
またy>0ならC>0、T>y^pとなり、x=p^(p−1)M^p+yはy^pより大きくできる。

有限和R_p(x,x−1)は隣接冪差x^p−(x−1)^pに等しく、その最後の項がx^(p−1)となる。
p≥2ならこの差はx以上。したがってy^p<xだけで007bのサイズ条件を満たす。
この明示的な構成により、一般の正のyについてサイズ条件を外部入力から除く。
pは奇素数、p∤yという条件は保持する。任意のFLT反例からの降下ではない。
-/

namespace DkMath.Lib.NumberTheory.PrimePowerCompensation.Lift

open DkMath.Lib.Cosmic DkMath.NumberTheory.GapFocusing

/-- [DkMath.Lib] 法Cと互いに素な、閾値Lを超えるための初等的な補助因子。
C>0ならC L+1>L。素数である必要はない。 -/
def padding (C L : ℕ) : ℕ := C * L + 1

/-- [DkMath.Lib] 補助因子は法の正性によらず常に正。 -/
theorem padding_pos (C L : ℕ) : 0 < padding C L := by unfold padding; omega

/-- [DkMath.Lib] 法Cの任意の素因数を補助因子から除く。合同式1のgcdによる表現。 -/
theorem padding_coprime (C L : ℕ) : (padding C L).Coprime C := by
  unfold padding
  exact (Nat.coprime_mul_left_add_left 1 C L).mpr (by simp)

/-- [DkMath.Lib] 法が正なら補助因子は指定閾値を厳密に超える。 -/
theorem lt_padding {C L : ℕ} (hC : 0 < C) : L < padding C L := by
  have h : 1 ≤ C := hC
  unfold padding
  nlinarith

/-- [DkMath.Lib] 隣接n乗の差は、n≥2、x≥1ならx以上。
有限和の最終項x^(n−1)を残すだけで十分な下界となる。 -/
theorem self_le_consecutive_power_gap {x n : ℕ} (hx : 1 ≤ x) (hn : 2 ≤ n) :
    x ≤ x ^ n - (x - 1) ^ n := by
  have h := geom_sum₂_mul_of_ge (Nat.sub_le x 1) n
  change powerDifferenceCofactor n x (x - 1) * (x - (x - 1)) = x ^ n - (x - 1) ^ n at h
  have hgap : x - (x - 1) = 1 := by omega
  rw [hgap, mul_one] at h
  have he : n - 1 + 1 = n := by omega
  have hs := powerDifferenceCofactor_succ (n - 1) x (x - 1)
  rw [he] at hs
  have hp : x ≤ x ^ (n - 1) := Nat.le_self_pow (by omega) x
  omega

/-- [DkMath.Lib] p乗因子をMへ入れることは、gapにそのp乗を掛ける操作になる。 -/
theorem gap_mul (p M T : ℕ) : gap p (M * T) = gap p M * T ^ p := by
  simp only [gap, mul_pow, mul_assoc]

/-- [DkMath.Lib] 正次数の冪とp^(p−1)の係数からM≤gapを得る。M=0でも成立。 -/
theorem le_gap {p : ℕ} (hp : p.Prime) (M : ℕ) : M ≤ gap p M := by
  have h1 := Nat.le_self_pow hp.ne_zero M
  have h2 : 1 ≤ p ^ (p - 1) := Nat.one_le_pow _ _ hp.one_lt.le
  unfold gap
  nlinarith

/-- [DkMath.Lib] 原始性と全制御素数の支持を保つ追加因子。 -/
def factor (p B y : ℕ) : ℕ := padding (p * Shift.primeProduct p B y * y) (y ^ p)

/-- [DkMath.Lib] 標準制御積へ追加因子を掛けた、サイズ条件を満たすパラメータ。 -/
def product (p B y : ℕ) : ℕ := Shift.primeProduct p B y * factor p B y

/-- [DkMath.Lib] 追加因子は正。 -/
theorem factor_pos (p B y : ℕ) : 0 < factor p B y := padding_pos _ _

/-- [DkMath.Lib] 拡大したパラメータも正。 -/
theorem product_pos (p B y : ℕ) : 0 < product p B y :=
  Nat.mul_pos (Shift.primeProduct_pos p B y) (factor_pos p B y)

/-- [DkMath.Lib] 追加因子はp、M₀、yの全支持から離れる。 -/
theorem factor_coprime (p B y : ℕ) :
    (factor p B y).Coprime (p * Shift.primeProduct p B y * y) := padding_coprime _ _

/-- [DkMath.Lib] 追加因子はyとの原始性を保つ。 -/
theorem factor_coprime_lower (p B y : ℕ) : (factor p B y).Coprime y :=
  Nat.Coprime.coprime_dvd_right (dvd_mul_left y _) (factor_coprime p B y)

/-- [DkMath.Lib] 標準積と追加因子の両方がyと互いに素なので、積も原始。 -/
theorem product_coprime_lower (p B y : ℕ) : (product p B y).Coprime y :=
  Nat.coprime_mul_iff_left.mpr ⟨Shift.primeProduct_coprime p B y, factor_coprime_lower p B y⟩

/-- [DkMath.Lib] p∤yの下で、拡大後のgapとyの原始性を実際に構成する。 -/
theorem gap_coprime {p B y : ℕ} (hp : p.Prime) (hpy : ¬ p ∣ y) :
    (gap p (product p B y)).Coprime y := by
  apply Shift.gap_coprime_of_mul_coprime
  exact Nat.coprime_mul_iff_left.mpr
    ⟨hp.coprime_iff_not_dvd.mpr hpy, product_coprime_lower p B y⟩

/-- [DkMath.Lib] p、M₀、yが正ならT>y^p。大きい素数やCRTの存在定理を要しない。 -/
theorem lower_pow_lt_factor {p B y : ℕ} (hp : p.Prime) (hy : 0 < y) :
    y ^ p < factor p B y :=
  lt_padding (Nat.mul_pos (Nat.mul_pos hp.pos (Shift.primeProduct_pos p B y)) hy)

/-- [DkMath.Lib] M₀≥1なのでT≤M₀T≤gap。 -/
theorem factor_le_gap {p B y : ℕ} (hp : p.Prime) : factor p B y ≤ gap p (product p B y) := by
  have hM := Shift.primeProduct_pos p B y
  have h : factor p B y ≤ product p B y := by unfold product; nlinarith
  exact h.trans (le_gap hp _)

/-- [DkMath.Lib] 明示的な追加因子により、007bで仮定したサイズ条件を達成する。
ここではp≥2だけを使い、奇数性やp∤yは局所算術の段階へ分離する。 -/
theorem size_condition {p B y : ℕ} (hp : p.Prime) (hy : 0 < y) :
    y ^ p < Shift.base p (product p B y) y ^ p -
      (Shift.base p (product p B y) y - 1) ^ p := by
  have h1 := lower_pow_lt_factor (B := B) hp hy
  have h2 := factor_le_gap (B := B) (y := y) hp
  have hx : 1 ≤ Shift.base p (product p B y) y := by unfold Shift.base; omega
  have h3 := self_le_consecutive_power_gap hx hp.two_le
  have h4 : gap p (product p B y) ≤ Shift.base p (product p B y) y := by
    unfold Shift.base
    omega
  omega

/-- [DkMath.Lib] 小素数はyを割る場合も含めC=pM₀yを割るので、追加因子を割らない。 -/
theorem small_prime_not_dvd_factor {p B y q : ℕ} (hp : p.Prime) (hq : q.Prime) (hB : q ≤ B) :
    ¬ q ∣ factor p B y := by
  have hd : q ∣ p * Shift.primeProduct p B y * y := by
    by_cases hqy : q ∣ y
    · exact dvd_mul_of_dvd_right hqy _
    · have hv := Shift.small_prime_product_valuation (y := y) hp hq hB hqy
      have hqM : q ∣ p * Shift.primeProduct p B y := dvd_of_one_le_padicValNat (by omega)
      exact dvd_mul_of_dvd_left hqM y
  have hc := Nat.Coprime.coprime_dvd_right hd (factor_coprime p B y)
  exact hq.coprime_iff_not_dvd.mp hc.symm

/-- [DkMath.Lib] 小素数q∤yは元のgapを割り、追加p乗因子を掛けた後も割る。 -/
theorem small_prime_dvd_gap {p B y q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hB : q ≤ B) (hqy : ¬ q ∣ y) : q ∣ gap p (product p B y) := by
  unfold product
  rw [gap_mul]
  exact dvd_mul_of_dvd_left (Shift.small_prime_dvd_gap hp hq hB hqy) _

/-- [DkMath.Lib] 追加因子は小素数の付値を増やさず、pMのq付値は1に保たれる。 -/
theorem small_prime_product_valuation {p B y q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hB : q ≤ B) (hqy : ¬ q ∣ y) : padicValNat q (p * product p B y) = 1 := by
  let : Fact q.Prime := ⟨hq⟩
  unfold product
  rw [← mul_assoc, padicValNat.mul
    (Nat.mul_ne_zero hp.ne_zero (Nat.ne_of_gt (Shift.primeProduct_pos p B y)))
    (Nat.ne_of_gt (factor_pos p B y)),
    padicValNat.eq_zero_of_not_dvd (small_prime_not_dvd_factor hp hq hB), add_zero]
  exact Shift.small_prime_product_valuation hp hq hB hqy

/-- [DkMath.Lib] サイズ条件を実現した後も小素数の正確な0/p付値を維持する。 -/
theorem small_prime_valuation_exact {p B y q : ℕ} (hp : p.Prime) (ho : Odd p)
    (hpy : ¬ p ∣ y) (hq : q.Prime) (hB : q ≤ B) :
    padicValNat q (Shift.base p (product p B y) y ^ p - y ^ p) = if q ∣ y then 0 else p := by
  have hc := gap_coprime (B := B) hp hpy
  split_ifs with hqy
  · exact padicValNat.eq_zero_of_not_dvd
      (Shift.not_dvd_difference_of_dvd_lower hp (product_pos p B y) hc hq hqy)
  · rw [Shift.local_valuation hp ho (product_pos p B y) hc hq (small_prime_dvd_gap hp hq hB hqy),
      small_prime_product_valuation hp hq hB hqy, mul_one]

/-- [DkMath.Lib] 小素数の全付値はpで割り切れる。yの素因数では付値0となる。 -/
theorem small_prime_local_completion {p B y q : ℕ} (hp : p.Prime) (ho : Odd p)
    (hpy : ¬ p ∣ y) (hq : q.Prime) (hB : q ≤ B) :
    p ∣ padicValNat q (Shift.base p (product p B y) y ^ p - y ^ p) := by
  rw [small_prime_valuation_exact hp ho hpy hq hB]
  split_ifs <;> simp

/-- [DkMath.Lib] 残余は全ての小素数を避ける。ここは局所算術だけを使う。 -/
theorem not_dvd_residual_of_small_prime {p B y q : ℕ} (hp : p.Prime) (ho : Odd p)
    (hpy : ¬ p ∣ y) (hq : q.Prime) (hB : q ≤ B) :
    ¬ q ∣ Shift.residual p (product p B y) y := by
  have hc := gap_coprime (B := B) hp hpy
  by_cases hqy : q ∣ y
  · exact Shift.not_dvd_residual_of_dvd_lower hp ho (product_pos p B y) hc hq hqy
  · exact Shift.not_dvd_residual_of_dvd_gap hp ho (product_pos p B y) hc hq
      (small_prime_dvd_gap hp hq hB hqy)

/-- [DkMath.Lib] 一般の正のyについて、サイズ条件を外部仮定にしない脱出定理。
実際に選んだ追加因子がサイズ条件と原始性を満たすため、007bを適用できる。 -/
theorem exists_prime_escape_with_address {p B y : ℕ} (hp : p.Prime) (ho : Odd p)
    (hy : 0 < y) (hpy : ¬ p ∣ y) :
    ∃ q, q.Prime ∧ B < q ∧ q ∣ Shift.residual p (product p B y) y ∧
      ¬ p ∣ padicValNat q (Shift.residual p (product p B y) y) ∧
      primeOrder q (Shift.base p (product p B y) y) y = p ∧ p ∣ q - 1 := by
  have hc := gap_coprime (B := B) hp hpy
  obtain ⟨q, hq, hqr, hv⟩ := exists_prime_padicValNat_not_dvd
    (Nat.ne_of_gt (Shift.residual_pos hp ho (product_pos p B y) hc))
    (Shift.residual_not_pow hp ho (product_pos p B y) hy hc (size_condition hp hy))
  have hB : B < q := by
    by_contra hn
    exact not_dvd_residual_of_small_prime hp ho hpy hq (by omega) hqr
  obtain ⟨hr, ha⟩ := Shift.residual_prime_address hp ho (product_pos p B y) hc hq hqr
  exact ⟨q, hq, hB, hqr, hv, hr, ha⟩

/-- [DkMath.Lib] 任意の有限集合と正の下側座標に対する同時構成。
pが奇素数かつp∤yという条件を残し、原始性とサイズ条件は内部で証明する。 -/
theorem finite_set_compensation_and_escape {p y : ℕ} (hp : p.Prime) (ho : Odd p)
    (hy : 0 < y) (hpy : ¬ p ∣ y) (S : Finset ℕ) :
    let M := product p (S.sup id) y
    (∀ q ∈ S, q.Prime → padicValNat q (Shift.base p M y ^ p - y ^ p) = if q ∣ y then 0 else p) ∧
      ∃ q, q.Prime ∧ q ∉ S ∧ q ∣ Shift.residual p M y ∧
        ¬ p ∣ padicValNat q (Shift.residual p M y) ∧
        primeOrder q (Shift.base p M y) y = p ∧ p ∣ q - 1 := by
  dsimp only
  constructor
  · intro q hq hprime
    exact small_prime_valuation_exact hp ho hpy hprime (Finset.le_sup (f := id) hq)
  · obtain ⟨q, hq, hB, hqr, hv, hr, ha⟩ :=
      exists_prime_escape_with_address (B := S.sup id) hp ho hy hpy
    exact ⟨q, hq, fun hmem => (not_le_of_gt hB) (Finset.le_sup (f := id) hmem),
      hqr, hv, hr, ha⟩


/-- [DkMath.Lib] pMの素因数はgapを割る。残余から係数の素数支持を除くための橋。 -/
theorem parameter_prime_dvd_gap {p M q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hd : q ∣ p * M) : q ∣ gap p M := by
  rcases hq.dvd_mul.mp hd with hqp | hqM
  · exact hqp.trans (prime_dvd_gap hp)
  · exact dvd_mul_of_dvd_right (dvd_pow hqM hp.ne_zero) _

/-- [DkMath.Lib] Kの素因数では、元の冪差の付値とKの付値が一致する。
qがpMを割るならgapを割りKと矛盾するため、補填係数の付値は0である。 -/
theorem difference_valuation_of_residual_prime {p M y q : ℕ} (hp : p.Prime) (ho : Odd p)
    (hM : 0 < M) (hc : (gap p M).Coprime y) (hq : q.Prime)
    (hqr : q ∣ Shift.residual p M y) :
    padicValNat q (Shift.base p M y ^ p - y ^ p) = padicValNat q (Shift.residual p M y) := by
  let : Fact q.Prime := ⟨hq⟩
  have hnot : ¬ q ∣ p * M := fun hd =>
    Shift.not_dvd_residual_of_dvd_gap hp ho hM hc hq (parameter_prime_dvd_gap hp hq hd) hqr
  rw [Shift.reconstruction hp ho hM hc, padicValNat.mul
    (pow_ne_zero _ (Nat.mul_ne_zero hp.ne_zero (Nat.ne_of_gt hM)))
    (Nat.ne_of_gt (Shift.residual_pos hp ho hM hc)), padicValNat.pow,
    padicValNat.eq_zero_of_not_dvd hnot, mul_zero, zero_add]

/-- [DkMath.Lib] 元の冪差にも上限外の未完成付値が残る。残余の主張から正確に戻す。
付値1ではなくpの倍数でないことを結論する。 -/
theorem exists_prime_escape_in_difference {p B y : ℕ} (hp : p.Prime) (ho : Odd p)
    (hy : 0 < y) (hpy : ¬ p ∣ y) :
    ∃ q, q.Prime ∧ B < q ∧ q ∣ Shift.base p (product p B y) y ^ p - y ^ p ∧
      ¬ p ∣ padicValNat q (Shift.base p (product p B y) y ^ p - y ^ p) ∧
      primeOrder q (Shift.base p (product p B y) y) y = p ∧ p ∣ q - 1 := by
  obtain ⟨q, hq, hB, hqr, hv, hr, ha⟩ := exists_prime_escape_with_address (B := B) hp ho hy hpy
  have hc := gap_coprime (B := B) hp hpy
  refine ⟨q, hq, hB, ?_, ?_, hr, ha⟩
  · rw [Shift.reconstruction hp ho (product_pos p B y) hc]
    exact dvd_mul_of_dvd_right hqr _
  · rw [difference_valuation_of_residual_prime hp ho (product_pos p B y) hc hq hqr]
    exact hv

/-- [DkMath.Lib] 有限個の局所付値の完済は、全体の完全冪性を決定しない。
任意の有限集合Sと許されたyについて、原始座標xを実際に構成し、
S内の正確な0/p付値と、全体の非完全冪性を同時に返す。 -/
theorem exists_primitive_nonpower_with_local_completion {p y : ℕ} (hp : p.Prime) (ho : Odd p)
    (hy : 0 < y) (hpy : ¬ p ∣ y) (S : Finset ℕ) :
    ∃ x, y < x ∧ x.Coprime y ∧ (¬ ∃ a : ℕ, a ^ p = x ^ p - y ^ p) ∧
      ∀ q ∈ S, q.Prime → padicValNat q (x ^ p - y ^ p) = if q ∣ y then 0 else p := by
  let M := product p (S.sup id) y
  have hc := gap_coprime (B := S.sup id) hp hpy
  refine ⟨Shift.base p M y, Shift.lt_base hp (product_pos p (S.sup id) y) y,
    Shift.base_coprime hc, Shift.difference_not_pow hp (product_pos p (S.sup id) y)
      hy (size_condition hp hy), ?_⟩
  intro q hq hprime
  exact small_prime_valuation_exact hp ho hpy hprime (Finset.le_sup (f := id) hq)

/-! ## 具体例と境界
追加因子は素数である必要はなく、制御集合の外の素数を含んでよい。
-/
example : padding 0 5 = 1 ∧ ¬ (5 < padding 0 5) := by decide
example : padding 6 8 = 49 ∧ (padding 6 8).Coprime 6 := by decide
example : factor 3 3 2 = 49 ∧ product 3 3 2 = 49 := by decide
example : Shift.base 3 (product 3 3 2) 2 = 1058843 := by decide

example : padicValNat 2 (Shift.base 3 (product 3 3 2) 2 ^ 3 - 2 ^ 3) = 0 := by
  rw [small_prime_valuation_exact (by decide) (by decide) (by decide) (by decide) (by decide)]
  decide
example : padicValNat 3 (Shift.base 3 (product 3 3 2) 2 ^ 3 - 2 ^ 3) = 3 := by
  rw [small_prime_valuation_exact (by decide) (by decide) (by decide) (by decide) (by decide)]
  decide

-- y=2の旧構成の脱出先7は追加因子49の支持へ入るため、新しい残余から除かれる。
example : ¬ 7 ∣ Shift.residual 3 (product 3 3 2) 2 :=
  Shift.not_dvd_residual_of_dvd_gap (by decide) (by decide) (product_pos 3 3 2)
    (gap_coprime (by decide) (by decide)) (by decide)
    (parameter_prime_dvd_gap (by decide) (by decide) (by decide))

-- 007bでサイズ条件が失敗したy=1001でも、追加因子を選んだ後は成立する。
example : 1001 ^ 3 < Shift.base 3 (product 3 3 1001) 1001 ^ 3 -
    (Shift.base 3 (product 3 3 1001) 1001 - 1) ^ 3 :=
  size_condition (by decide) (by decide)

example : (gap 3 (product 3 3 1001)).Coprime 1001 :=
  gap_coprime (by decide) (by decide)

-- サイズ不等式自体はp=2でも成立する。奇素数条件はLTEと残余の支持除去に必要。
example : 1 ^ 2 < Shift.base 2 (product 2 3 1) 1 ^ 2 -
    (Shift.base 2 (product 2 3 1) 1 - 1) ^ 2 := size_condition (by decide) (by decide)

example (B : ℕ) : ∃ q, q.Prime ∧ B < q ∧ q ∣ Shift.residual 3 (product 3 B 1001) 1001 ∧
    ¬ 3 ∣ padicValNat q (Shift.residual 3 (product 3 B 1001) 1001) ∧
    primeOrder q (Shift.base 3 (product 3 B 1001) 1001) 1001 = 3 ∧ 3 ∣ q - 1 :=
  exists_prime_escape_with_address (by decide) (by decide) (by decide) (by decide)

example (S : Finset ℕ) : ∃ x, 2 < x ∧ x.Coprime 2 ∧ (¬ ∃ a : ℕ, a ^ 3 = x ^ 3 - 2 ^ 3) ∧
    ∀ q ∈ S, q.Prime → padicValNat q (x ^ 3 - 2 ^ 3) = if q ∣ 2 then 0 else 3 :=
  exists_primitive_nonpower_with_local_completion (by decide) (by decide) (by decide) (by decide) S

end DkMath.Lib.NumberTheory.PrimePowerCompensation.Lift
