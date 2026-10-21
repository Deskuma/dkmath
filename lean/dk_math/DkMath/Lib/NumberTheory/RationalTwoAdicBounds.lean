/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_FreyPackage_freyCurve_rational_p_torsion_eq_zero.lean, S04 valuation lemmas.
Upstream blob: fe61fd5d4f94d55b5a9da38d1541903c84397df0
Modified for DkMath: separate zero-tolerant bounds from exact nonzero values,
use descriptive APIs, and isolate the arithmetic from Frey and torsion.
-/

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

#print "file: DkMath.Lib.NumberTheory.RationalTwoAdicBounds"

/-!
# 有理数の2進付値: 下界と正確な深さを区別する

Mathlibの`padicValRat 2 0`は便宜的に0を返す。しかし付値の加法公式は、
零を含めて通常の整数等式として使えるわけではない。
`Lower n q`はq=0またはn≤v₂(q)、`Exact n q`はq≠0かつv₂(q)=nと定義する。
零を許す整性・下界の計算と、非零での正確な付値計算をこの二つで分離する。

和差で付値が異なる場合は、低い方が正確に残り非零となる。
同じ付値なら打ち消しを許す下界だけを使う。さらに2進単元は法2で1となるため、
二つの単元の和差は深さ1以上になる。これらは楕円曲線を使わない有理数の定理である。
-/
namespace DkMath.Lib.NumberTheory.RationalTwoAdicBounds
local notation "v" => padicValRat 2

/-- 零を許す2進付値の下界。零でのpadicValRatの便宜値を使わない。 -/
def Lower (n : ℤ) (q : ℚ) : Prop := q = 0 ∨ n ≤ v q

/-- 零は全ての深さの下界を満たす。 -/
lemma Lower.zero (n : ℤ) : Lower n 0 := Or.inl rfl

/-- 下界は弱められる。零の場合も保持する。 -/
lemma Lower.mono {n m : ℤ} {q : ℚ} (h : Lower m q) (hnm : n ≤ m) : Lower n q := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (le_trans hnm h)

/-- 符号を反転しても付値の下界は変わらない。 -/
lemma Lower.neg {n : ℤ} {q : ℚ} (h : Lower n q) : Lower n (-q) := by
  rcases h with h | h
  · exact Or.inl (by rw [h, _root_.neg_zero])
  · exact Or.inr (by rwa [padicValRat.neg])

/-- 同じ深さの二数の和もその深さ以上。和が零になる場合を許す。 -/
lemma Lower.add {n : ℤ} {q r : ℚ} (hq : Lower n q) (hr : Lower n r) : Lower n (q + r) := by
  by_cases hqr : q + r = 0
  · exact Or.inl hqr
  rcases hq with hq | hq
  · subst hq; simpa using hr
  rcases hr with hr | hr
  · subst hr; simp only [add_zero]; exact Or.inr hq
  exact Or.inr (le_trans (le_min hq hr) (padicValRat.min_le_padicValRat_add hqr))

/-- 差の下界。打ち消しにより零となることを除外しない。 -/
lemma Lower.sub {n : ℤ} {q r : ℚ} (hq : Lower n q) (hr : Lower n r) : Lower n (q - r) := by
  rw [sub_eq_add_neg]; exact Lower.add hq (Lower.neg hr)

/-- 積の下界は加算される。零因子を先に処理する。 -/
lemma Lower.mul {n m : ℤ} {q r : ℚ} (hq : Lower n q) (hr : Lower m r) : Lower (n + m) (q * r) := by
  rcases hq with hq | hq
  · exact Or.inl (by rw [hq, zero_mul])
  rcases hr with hr | hr
  · exact Or.inl (by rw [hr, mul_zero])
  by_cases hq0 : q = 0
  · exact Or.inl (by rw [hq0, zero_mul])
  by_cases hr0 : r = 0
  · exact Or.inl (by rw [hr0, mul_zero])
  exact Or.inr (by rw [padicValRat.mul hq0 hr0]; omega)

/-- 平方の下界は元の二倍。 -/
lemma Lower.square {n : ℤ} {q : ℚ} (hq : Lower n q) : Lower (n + n) (q ^ 2) := by
  rw [pow_two]; exact Lower.mul hq hq

/-- 整数は2進的に整である。整数0も含む。 -/
lemma lower_int (z : ℤ) : Lower 0 (z : ℚ) := by
  by_cases hz : (z : ℚ) = 0
  · exact Or.inl hz
  · exact Or.inr (by rw [padicValRat.of_int]; exact_mod_cast Nat.zero_le _)

/-- 自然数も2進的に整である。 -/
lemma lower_nat (k : ℕ) : Lower 0 (k : ℚ) := by
  have := lower_int (k : ℤ); simpa using this

/-- 2は深さ1の下界を満たす。 -/
lemma lower_two : Lower 1 (2 : ℚ) := by
  right; rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]; simp

/-- 素数2自身の付値は1である。 -/
lemma valuation_two : v (2 : ℚ) = 1 := by
  rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, padicValRat.self (by norm_num)]

/-- 非零性と正確な2進付値を同時に保持する。零はどの深さでもExactではない。 -/
def Exact (n : ℤ) (q : ℚ) : Prop := q ≠ 0 ∧ v q = n

/-- 正確な付値から同じ深さの下界へ忘却する。 -/
lemma Exact.lower {n : ℤ} {q : ℚ} (h : Exact n q) : Lower n q := Or.inr h.2.ge

/-- 非零な二数の積の付値は加算される。 -/
lemma Exact.mul {n m : ℤ} {q r : ℚ} (hq : Exact n q) (hr : Exact m r) : Exact (n + m) (q * r) :=
  ⟨mul_ne_zero hq.1 hr.1, by rw [padicValRat.mul hq.1 hr.1, hq.2, hr.2]⟩

/-- 非零な平方の付値を二倍する。 -/
lemma Exact.square {n : ℤ} {q : ℚ} (hq : Exact n q) : Exact (n + n) (q ^ 2) := by
  rw [pow_two]; exact Exact.mul hq hq

/-- 分母と分子の非零性を保持した商の正確な付値。 -/
lemma Exact.div {n m : ℤ} {q r : ℚ} (hq : Exact n q) (hr : Exact m r) : Exact (n - m) (q / r) :=
  ⟨div_ne_zero hq.1 hr.1, by rw [padicValRat.div hq.1 hr.1, hq.2, hr.2]⟩

/-- 符号反転は非零性と正確な付値を保つ。 -/
lemma Exact.neg {n : ℤ} {q : ℚ} (hq : Exact n q) : Exact n (-q) :=
  ⟨neg_ne_zero.mpr hq.1, by rw [padicValRat.neg, hq.2]⟩

/-- 低い付値の非零項と、厳密に高い深さの項を足すと低い付値が残る。
和の非零性もここで証明するので、呼出側で付値の加法則を無条件に使う必要はない。 -/
lemma Exact.add_lower {n m : ℤ} {q r : ℚ} (hq : Exact n q) (hr : Lower m r) (hnm : n < m) : Exact n (q + r) := by
  rcases hr with hr | hr
  · subst hr; simpa using hq
  by_cases hr0 : r = 0
  · subst hr0; simpa using hq
  have hlt : v q < v r := by rw [hq.2]; omega
  have hqr : q + r ≠ 0 := by
    intro h
    have : r = -q := by linear_combination h
    rw [this, padicValRat.neg] at hlt
    exact lt_irrefl _ hlt
  exact ⟨hqr, by rw [padicValRat.add_eq_of_lt hqr hq.1 hr0 hlt, hq.2]⟩

/-- 高い深さの項を先に書いた、和の正確な付値。 -/
lemma Lower.add_exact {n m : ℤ} {q r : ℚ} (hq : Lower m q) (hr : Exact n r) (hnm : n < m) : Exact n (q + r) := by
  rw [add_comm]; exact Exact.add_lower hr hq hnm

/-- 低い付値の項から高い深さの項を引いても正確な付値は変わらない。 -/
lemma Exact.sub_lower {n m : ℤ} {q r : ℚ} (hq : Exact n q) (hr : Lower m r) (hnm : n < m) : Exact n (q - r) := by
  rw [sub_eq_add_neg]; exact Exact.add_lower hq (Lower.neg hr) hnm

/-- 高い深さの項から低い付値の項を引いた場合も低い付値が残る。 -/
lemma Lower.sub_exact {n m : ℤ} {q r : ℚ} (hq : Lower m q) (hr : Exact n r) (hnm : n < m) : Exact n (q - r) := by
  rw [sub_eq_add_neg]; exact Lower.add_exact hq (Exact.neg hr) hnm

/-- ある正確な深さは、それより厳密に深い下界と両立しない。 -/
lemma Exact.not_lower {n m : ℤ} {q : ℚ} (hq : Exact n q) (hq' : Lower m q) (hnm : n < m) : False := by
  rcases hq' with h | h
  · exact hq.1 h
  · rw [hq.2] at h; omega

/-- 有理2進単元は法2で1に等しい。
既約分数の分子と分母がともに奇数であることを示し、その差の偶数性へ戻す。 -/
lemma lower_one_sub_one_of_unit {q : ℚ} (hq : Exact 0 q) : Lower 1 (q - 1) := by
  obtain ⟨hq0, hv⟩ := hq
  have hnum : q.num ≠ 0 := Rat.num_ne_zero.mpr hq0
  have hden : q.den ≠ 0 := q.den_ne_zero
  have hdef : v q = padicValInt 2 q.num - padicValNat 2 q.den := padicValRat_def 2 q
  have hcop : Nat.Coprime q.num.natAbs q.den := q.reduced
  have hn2 : ¬ (2 : ℤ) ∣ q.num := by
    intro h2
    have hd2 : ¬ 2 ∣ q.den := by
      intro hd
      have h2' : 2 ∣ q.num.natAbs := by
        rcases h2 with ⟨k, hk⟩; exact ⟨k.natAbs, by rw [hk, Int.natAbs_mul]; rfl⟩
      have := Nat.eq_one_of_dvd_coprimes hcop h2' hd
      omega
    have hvd : padicValNat 2 q.den = 0 := padicValNat.eq_zero_of_not_dvd hd2
    have hvn : 1 ≤ padicValInt 2 q.num := by
      have := (padicValInt_dvd_iff (p := 2) 1 q.num).mp
        (by simpa only [pow_one, Nat.cast_ofNat] using h2)
      rcases this with h | h
      · exact absurd h hnum
      · exact h
    rw [hvd] at hdef; omega
  have hvn : padicValInt 2 q.num = 0 := padicValInt.eq_zero_of_not_dvd hn2
  have hvd : padicValNat 2 q.den = 0 := by rw [hvn] at hdef; omega
  have hd2 : ¬ 2 ∣ q.den := by
    intro hd
    have := one_le_padicValNat_of_dvd hden hd
    omega
  have hd0 : (q.den : ℚ) ≠ 0 := by exact_mod_cast hden
  have hq_eq : q - 1 = ((q.num - q.den : ℤ) : ℚ) / (q.den : ℚ) := by
    push_cast
    rw [sub_div, div_self hd0, Rat.num_div_den q]
  by_cases hnd : (q.num - q.den : ℤ) = 0
  · left; rw [hq_eq, hnd]; simp
  right
  have heven : (2 : ℤ) ∣ q.num - q.den := by
    have hn_odd : Odd q.num := Int.not_even_iff_odd.mp (fun h => hn2 (even_iff_two_dvd.mp h))
    have hd_odd : Odd (q.den : ℤ) := by
      have : Odd q.den := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hd2)
      exact (Int.odd_coe_nat _).mpr this
    exact even_iff_two_dvd.mp (Odd.sub_odd hn_odd hd_odd)
  have hnd0 : ((q.num - q.den : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hnd
  rw [hq_eq, padicValRat.div hnd0 hd0, padicValRat.of_int, padicValRat.of_nat, hvd]
  have h1 : 1 ≤ padicValInt 2 (q.num - q.den) := by
    rcases (padicValInt_dvd_iff (p := 2) 1 (q.num - q.den)).mp
        (by simpa only [pow_one, Nat.cast_ofNat] using heven) with h | h
    · exact absurd h hnd
    · exact h
  push_cast
  omega

/-- 2進単元に深さ1以上の項を加えても単元である。 -/
lemma unit_add_lower {q r : ℚ} (hq : Exact 0 q) (hr : Lower 1 r) : Exact 0 (q + r) := Exact.add_lower hq hr (by norm_num)

/-- 二つの2進単元の和は深さ1以上。和が零になる場合も含む。 -/
lemma lower_one_add_of_units {q r : ℚ} (hq : Exact 0 q) (hr : Exact 0 r) : Lower 1 (q + r) := by
  have h1 := lower_one_sub_one_of_unit hq
  have h2 := lower_one_sub_one_of_unit hr
  have : q + r = (q - 1) + (r - 1) + 2 := by ring
  rw [this]
  exact Lower.add (Lower.add h1 h2) lower_two

/-- 二つの2進単元の差は深さ1以上。 -/
lemma lower_one_sub_of_units {q r : ℚ} (hq : Exact 0 q) (hr : Exact 0 r) : Lower 1 (q - r) := by
  have h1 := lower_one_sub_one_of_unit hq
  have h2 := lower_one_sub_one_of_unit hr
  have : q - r = (q - 1) - (r - 1) := by ring
  rw [this]
  exact Lower.sub h1 h2

/-- 2進整なqについて連続する二数q,q+1の積は深さ1以上。 -/
lemma lower_one_mul_add_one {q : ℚ} (hq : Lower 0 q) : Lower 1 (q * (q + 1)) := by
  by_cases hq0 : q = 0
  · exact Or.inl (by rw [hq0, zero_mul])
  rcases hq with h | h
  · exact absurd h hq0
  by_cases hv : v q = 0
  · have hu : Exact 0 q := ⟨hq0, hv⟩
    have h1 : Lower 1 (q + 1) := by
      have : q + 1 = (q - 1) + 2 := by ring
      rw [this]; exact Lower.add (lower_one_sub_one_of_unit hu) lower_two
    have := Lower.mul (Or.inr h : Lower 0 q) h1
    simpa using this
  · have hq1 : Lower 1 q := Or.inr (by omega)
    have h1 : Lower 0 (q + 1) := Lower.add (Or.inr h) (by exact_mod_cast lower_int 1)
    have := Lower.mul hq1 h1
    simpa using this

/-- 零を許す分子と、非零かつ正確な付値を持つ分母の商の下界。 -/
lemma Lower.div_exact {n m : ℤ} {q r : ℚ} (hq : Lower n q) (hr : Exact m r) : Lower (n - m) (q / r) := by
  rcases hq with hq | hq
  · exact Or.inl (by rw [hq, zero_div])
  by_cases hq0 : q = 0
  · exact Or.inl (by rw [hq0, zero_div])
  exact Or.inr (by rw [padicValRat.div hq0 hr.1, hr.2]; omega)

/-- 正確な付値データから非零性を取り出す。 -/
lemma Exact.ne {n : ℤ} {q : ℚ} (h : Exact n q) : q ≠ 0 := h.1

/-- 非零な有理数は自身の付値についてExactである。 -/
lemma exact_valuation {q : ℚ} (hq : q ≠ 0) : Exact (v q) q := ⟨hq, rfl⟩

/-- 3は2進単元である。 -/
lemma exact_three : Exact 0 (3 : ℚ) := by
  refine ⟨by norm_num, ?_⟩
  rw [show (3 : ℚ) = ((3 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]
  simp [padicValNat.eq_zero_of_not_dvd (show ¬ 2 ∣ 3 by omega)]

/-- 2の正確な付値と非零性。 -/
lemma exact_two : Exact 1 (2 : ℚ) := ⟨by norm_num, valuation_two⟩

/-- 4の正確な付値は2である。 -/
lemma exact_four : Exact 2 (4 : ℚ) := by
  have := Exact.mul exact_two exact_two; norm_num at this; exact this

/-- 16の正確な付値は4である。 -/
lemma exact_sixteen : Exact 4 (16 : ℚ) := by
  have := Exact.mul exact_four exact_four; norm_num at this; exact this

/-- 非零の自然数冪の正確な付値。k=0でも1の付値0となる。 -/
lemma Exact.pow {n : ℤ} {q : ℚ} (hq : Exact n q) (k : ℕ) : Exact (k * n) (q ^ k) :=
  ⟨pow_ne_zero _ hq.1, by rw [padicValRat.pow, hq.2]⟩

/-- 零も含めた自然数冪の下界。k=0ではq=0であってもq⁰=1を正しく扱う。 -/
lemma Lower.pow {n : ℤ} {q : ℚ} (hq : Lower n q) (k : ℕ) : Lower (k * n) (q ^ k) := by
  induction k with
  | zero => exact Or.inr (by simp)
  | succ k ih =>
    simpa only [pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using ih.mul hq

/-- 異なる下界を持つ和には、両者のminを共通の下界として使える。 -/
lemma Lower.add_min {n m : ℤ} {q r : ℚ} (hq : Lower n q) (hr : Lower m r) :
    Lower (min n m) (q + r) :=
  (hq.mono (min_le_left n m)).add (hr.mono (min_le_right n m))

/-- 和と同様に、差の下界もminで与えられる。零になる場合も許す。 -/
lemma Lower.sub_min {n m : ℤ} {q r : ℚ} (hq : Lower n q) (hr : Lower m r) :
    Lower (min n m) (q - r) := by
  rw [sub_eq_add_neg]
  exact hq.add_min hr.neg

/-- 零を許す下界から、非零性を明示した時だけ数値的な付値不等式を取り出す。 -/
lemma Lower.le_valuation {n : ℤ} {q : ℚ} (h : Lower n q) (hq : q ≠ 0) : n ≤ v q :=
  h.resolve_left hq

/-- 深さの異なる非零な二数の和の正確な付値はminである。 -/
lemma Exact.add_exact_of_ne {n m : ℤ} {q r : ℚ} (hq : Exact n q) (hr : Exact m r)
    (hne : n ≠ m) : Exact (min n m) (q + r) := by
  rcases lt_or_gt_of_ne hne with h | h
  · rw [min_eq_left h.le]
    exact hq.add_lower hr.lower h
  · rw [min_eq_right h.le]
    exact hq.lower.add_exact hr h

/-- 深さの異なる非零な二数の差でも、正確な付値はminである。 -/
lemma Exact.sub_exact_of_ne {n m : ℤ} {q r : ℚ} (hq : Exact n q) (hr : Exact m r)
    (hne : n ≠ m) : Exact (min n m) (q - r) := by
  rw [sub_eq_add_neg]
  exact hq.add_exact_of_ne hr.neg hne

end DkMath.Lib.NumberTheory.RationalTwoAdicBounds
