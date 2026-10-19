/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyPrimeProfile
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.RingTheory.Coprime.Lemmas

#print "file: DkMath.FLT.FreyCounterexample"

/-!
# NOTE-009: 任意の非零整数反例からFrey Sourceへ

共通因子dを除き、元の座標a=dA,b=dB,c=dCを記録する。
原始解の偶数座標を第二変数に移し、奇数冪の負号を利用して方程式を保持する。
最後に全座標の符号を同時に選び、第一変数を3 mod4へ向ける。
分母条件を既存の `ofOriented` で証明し、同じSourceの局所最小性へ渡す。
反例の存在もFLTの終点も使わない。正規化で座標は変わるので、共通因子と
符号付き置換の証拠を公開し、元の反例と同じ座標だとは主張しない。
-/
namespace DkMath.FLT.Frey

/-- 冪和と三変数のgcd=1から、左の二変数のBézout原始性を得る。 -/
theorem coprime_of_primitive_equation {p : ℕ} (hp : 0 < p) {a b c : ℤ}
    (ha : a ≠ 0) (hg : ({a, b, c} : Finset ℤ).gcd id = 1)
    (he : a ^ p + b ^ p = c ^ p) : IsCoprime a b := by
  apply isCoprime_of_prime_dvd
  · rintro ⟨rfl, _⟩
    exact ha rfl
  · intro q hq hqa hqb
    have hqc : q ∣ c := hq.dvd_of_dvd_pow (n := p) (by
      rw [← he]
      exact dvd_add (dvd_pow hqa hp.ne') (dvd_pow hqb hp.ne'))
    apply hq.not_dvd_one
    rw [← hg]
    apply Finset.dvd_gcd_iff.mpr
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption

/-- 共通因子と原始解を同時に保持する記録。元の整数反例との等式を捨てない。 -/
structure PrimitiveReduction (p : ℕ) (a b c : ℤ) where
  scale : ℤ
  scale_ne : scale ≠ 0
  A : ℤ
  B : ℤ
  C : ℤ
  a_eq : a = scale * A
  b_eq : b = scale * B
  c_eq : c = scale * C
  A_ne : A ≠ 0
  B_ne : B ≠ 0
  C_ne : C ≠ 0
  coprime : IsCoprime A B
  equation : A ^ p + B ^ p = C ^ p

/-- 有限集合のgcdを抽出して、非原始反例を原始化する。
同じ非零dのp乗を消去し、得た方程式から二変数の原始性を証明する。 -/
theorem exists_primitiveReduction {p : ℕ} (hp : 0 < p) {a b c : ℤ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (he : a ^ p + b ^ p = c ^ p) :
    Nonempty (PrimitiveReduction p a b c) := by
  classical
  let s : Finset ℤ := {a, b, c}
  let d := s.gcd id
  obtain ⟨f, hf, hfg⟩ := s.extract_gcd id (by simp [s])
  have hA : a = d * f a := hf a (by simp [s])
  have hB : b = d * f b := hf b (by simp [s])
  have hC : c = d * f c := hf c (by simp [s])
  have hd : d ≠ 0 := by intro hz; exact ha (by rw [hA, hz, zero_mul])
  have hfa : f a ≠ 0 := by intro hz; exact ha (by rw [hA, hz, mul_zero])
  have hfb : f b ≠ 0 := by intro hz; exact hb (by rw [hB, hz, mul_zero])
  have hfc : f c ≠ 0 := by intro hz; exact hc (by rw [hC, hz, mul_zero])
  have hfe : (f a) ^ p + (f b) ^ p = (f c) ^ p := by
    rw [hA, hB, hC, mul_pow, mul_pow, mul_pow, ← mul_add] at he
    exact mul_left_cancel₀ (pow_ne_zero p hd) he
  have hfg' : ({f a, f b, f c} : Finset ℤ).gcd id = 1 := by
    rw [Finset.gcd_eq_gcd_image] at hfg
    simpa [s] using hfg
  exact ⟨⟨d, hd, f a, f b, f c, hA, hB, hC, hfa, hfb, hfc,
    coprime_of_primitive_equation hp hfa hfg' hfe, hfe⟩⟩

/-- 原始冪和の右辺は左辺の各変数と互いに素。向き付けの置換時に利用する。 -/
theorem coprime_right_of_equation {p : ℕ} (hp : 0 < p) {a b c : ℤ}
    (he : a ^ p + b ^ p = c ^ p) (hab : IsCoprime a b) :
    IsCoprime a c ∧ IsCoprime b c := by
  have hac : IsCoprime (a ^ p) (c ^ p) := by
    convert (hab.pow (m := p) (n := p)).add_mul_left_right 1 using 1
    rw [mul_one, add_comm, he]
  have hbc : IsCoprime (b ^ p) (c ^ p) := by
    convert (hab.symm.pow (m := p) (n := p)).add_mul_left_right 1 using 1
    rw [mul_one, he]
  exact ⟨(IsCoprime.pow_iff hp hp).mp hac, (IsCoprime.pow_iff hp hp).mp hbc⟩

/-- 偶数を第二座標にする三種類の正確な置換。右辺を左辺へ移す時だけ負号を伴う。 -/
def ParityTrace (a b c x y z : ℤ) : Prop :=
  (x, y, z) = (a, b, c) ∨ (x, y, z) = (b, a, c) ∨ (x, y, z) = (a, -c, -b)

/-- 方程式・非零性・原始性を保ち、奇数／偶数の順に並べる。 -/
theorem orient_parity {p : ℕ} (hp : Odd p) (hp0 : 0 < p) {a b c : ℤ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : IsCoprime a b)
    (he : a ^ p + b ^ p = c ^ p) :
    ∃ x y z : ℤ, x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ IsCoprime x y ∧
      x ^ p + y ^ p = z ^ p ∧ Odd x ∧ Even y ∧ ParityTrace a b c x y z := by
  have hnot : ¬ (Even a ∧ Even b) := by
    rintro ⟨hea, heb⟩
    have hu := hab.isUnit_of_dvd' (even_iff_two_dvd.mp hea) (even_iff_two_dvd.mp heb)
    rcases Int.isUnit_iff.mp hu with h | h <;> norm_num at h
  by_cases heb : Even b
  · exact ⟨a, b, c, ha, hb, hc, hab, he,
      Int.not_even_iff_odd.mp (fun hea => hnot ⟨hea, heb⟩), heb, Or.inl rfl⟩
  by_cases hea : Even a
  · exact ⟨b, a, c, hb, ha, hc, hab.symm, by simpa [add_comm] using he,
      Int.not_even_iff_odd.mp heb, hea, Or.inr (Or.inl rfl)⟩
  have hec : Even c := by
    apply (Int.even_pow' hp0.ne').mp
    rw [← he, Int.even_add]
    simp only [Int.even_pow' hp0.ne', hea, heb]
  refine ⟨a, -c, -b, ha, neg_ne_zero.mpr hc, neg_ne_zero.mpr hb,
    (coprime_right_of_equation hp0 he hab).1.neg_right, ?_,
    Int.not_even_iff_odd.mp hea, hec.neg, Or.inr (Or.inr rfl)⟩
  rw [hp.neg_pow, hp.neg_pow]
  linear_combination he

/-- 全符号の同時変更と三種類の置換を記録する。元との関係を抽象的な存在に隠さない。 -/
def OrientationTrace (a b c x y z : ℤ) : Prop :=
  ∃ e : ℤ, (e = 1 ∨ e = -1) ∧ ParityTrace (e * a) (e * b) (e * c) x y z

/-- 奇整数は、符号を選べば3 mod4となる。指数やFermat方程式を必要としない。 -/
theorem odd_mod_four_orientation {x : ℤ} (hx : Odd x) :
    4 ∣ x + 1 ∨ 4 ∣ -x + 1 := by
  have h2 := Int.odd_iff.mp hx
  have hm : x % 4 = 1 ∨ x % 4 = 3 := by omega
  rcases hm with h | h
  · right
    rw [Int.dvd_iff_emod_eq_zero]
    omega
  · left
    rw [Int.dvd_iff_emod_eq_zero]
    omega

/-- 原始反例を第一座標3 mod4・第二座標偶数へ向け、分母条件まで証明する。 -/
theorem exists_source_of_coprime {p : ℕ} (hp : Odd p) (hp4 : 4 ≤ p) {a b c : ℤ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : IsCoprime a b)
    (he : a ^ p + b ^ p = c ^ p) :
    ∃ S : Source p, 4 ∣ S.a + 1 ∧ Even S.b ∧ OrientationTrace a b c S.a S.b S.c := by
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxyz, hxo, hye, htrace⟩ :=
    orient_parity hp (by omega) ha hb hc hab he
  rcases odd_mod_four_orientation hxo with hx4 | hnx4
  · refine ⟨ofOriented hp hp4 x y z hx hy hz hxy hxyz hx4 hye, hx4, hye, 1, Or.inl rfl, ?_⟩
    simpa only [one_mul, ofOriented] using htrace
  · have hneg : (-x) ^ p + (-y) ^ p = (-z) ^ p := by rw [hp.neg_pow, hp.neg_pow, hp.neg_pow]; omega
    refine ⟨ofOriented hp hp4 (-x) (-y) (-z) (neg_ne_zero.mpr hx) (neg_ne_zero.mpr hy)
      (neg_ne_zero.mpr hz) hxy.neg_left.neg_right hneg hnx4 hye.neg,
      hnx4, hye.neg, -1, Or.inr rfl, ?_⟩
    simp only [ParityTrace, Prod.mk.injEq] at htrace ⊢
    rcases htrace with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> simp [ofOriented]

/-- 任意の非零整数反例からSourceを構成でき、元との共通因子・符号付き置換を残す。 -/
theorem exists_source_of_counterexample {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {a b c : ℤ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (he : a ^ p + b ^ p = c ^ p) :
    ∃ S : Source p, 4 ∣ S.a + 1 ∧ Even S.b ∧
      ∃ R : PrimitiveReduction p a b c, OrientationTrace R.A R.B R.C S.a S.b S.c := by
  obtain ⟨R⟩ := exists_primitiveReduction hp.pos ha hb hc he
  obtain ⟨S, h4, heven, ht⟩ := exists_source_of_coprime
    (hp.odd_of_ne_two (by omega)) (by omega) R.A_ne R.B_ne R.C_ne R.coprime R.equation
  exact ⟨S, h4, heven, R, ht⟩

/-- 提案された公開入口。反例からのみSourceを選び、FLT終点による空虚な構成をしない。 -/
noncomputable def Source.ofCounterexample (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (he : a ^ p + b ^ p = c ^ p) : Source p :=
  (exists_source_of_counterexample hp hp5 ha hb hc he).choose

/-- 選択した同じSourceの向き付けと、元の反例に対する完全な正規化証拠。 -/
theorem Source.ofCounterexample_spec (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (he : a ^ p + b ^ p = c ^ p) :
    let S := Source.ofCounterexample p hp hp5 a b c ha hb hc he
    4 ∣ S.a + 1 ∧ Even S.b ∧
      ∃ R : PrimitiveReduction p a b c, OrientationTrace R.A R.B R.C S.a S.b S.c :=
  (exists_source_of_counterexample hp hp5 ha hb hc he).choose_spec

/-- 任意の非零整数反例から選んだ同じSourceについて、正式な全素数最小性・半安定性と
最小判別式のp倍性分類を一度に得る。残余表現・導手・モジュラー性は含めない。 -/
theorem Source.ofCounterexample_local_profile (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (he : a ^ p + b ^ p = c ^ p) :
    let S := Source.ofCounterexample p hp hp5 a b c ha hb hc he
    S.rationalCurve.IsElliptic ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime],
      WeierstrassCurve.IsMinimal (DkMath.Lib.NumberTheory.FreyLocalReduction.LocalRing ℓ) S.rationalCurve ∧
      (WeierstrassCurve.HasGoodReduction (DkMath.Lib.NumberTheory.FreyLocalReduction.LocalRing ℓ) S.rationalCurve ∨
        WeierstrassCurve.HasMultiplicativeReduction
          (DkMath.Lib.NumberTheory.FreyLocalReduction.LocalRing ℓ) S.rationalCurve) ∧
      ((p : ℤ) ∣ padicValRat ℓ S.rationalCurve.Δ ↔ ℓ ≠ 2) := by
  let S := Source.ofCounterexample p hp hp5 a b c ha hb hc he
  let : Fact p.Prime := ⟨hp⟩
  refine ⟨S.rationalCurve_isElliptic, ?_⟩
  intro ℓ hℓ
  exact ⟨S.isMinimal_every_prime hp.pos, S.good_or_multiplicative_every_prime hp.pos,
    S.exponent_dvd_valuation_iff_ne_two hp5⟩

end DkMath.FLT.Frey
