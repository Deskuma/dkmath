/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.Basic
import DkMath.Lib.NumberTheory.FreyGapCubic
import Mathlib.FieldTheory.Finite.Basic

#print "file: DkMath.NumberTheory.Legendre.FreyC4CentralSeat"

/-!
# NOTE-006 §3: Legendre の中央席と Frey の c₄

Qₙ=n²+n+1 を、既存の平方殻のオフセット n+1 として定義する。
整数モデル Eₙ: y²=x(x−n)(x+1) では c₄=16Qₙ、Δ=16n²(n+1)²。
有理数上の正規化モデル Wₙ では c₄=Qₙ となる。16を落としてよいのはモデルを
変えた後であり、Wₙ の整係数性は一般の n では保証されない。

Qₙ と n(n+1) は互いに素なので、その素因子 q は Eₙ の判別式を割らない。
実際に ZMod q へ写した曲線の非特異性と c₄=0 を同時に得る。
q≠3 の場合、n mod q の乗法位数が3となり、3∣q−1 が従う。
これは与えられた素因子の分類であり、Qₙ の素数性・平方殻内の素数の存在・
全被覆の排除・Legendre 予想を結論しない。FLT の反例仮定も用いない。
-/

namespace DkMath.NumberTheory.Legendre.FreyC4CentralSeat

open DkMath.Lib.NumberTheory

/-- 平方殻の上側中央席。既存の点 n²+r に r=n+1 を代入した値である。 -/
def centralSeat (n : ℕ) : ℕ := n ^ 2 + n + 1

/-- 平方殻 API の点の座標と同じ値を持つ。 -/
theorem centralSeat_eq_square_add (n : ℕ) : centralSeat n = n ^ 2 + (n + 1) := by
  simp only [centralSeat, Nat.add_assoc]

/-- n>0 なら中央席のオフセットは開いた平方殻の内部にある。
n=0 の Q₀=1 は上端なので、この前提を除くことはできない。 -/
theorem centralSeat_offset {n : ℕ} (hn : 0 < n) : SquareOffset n (n + 1) := by
  unfold SquareOffset
  omega

/-- 自然数の中央席を、既存の平方区間の述語へ直接接続する。 -/
theorem centralSeat_mem_squareCell {n : ℕ} (hn : 0 < n) : SquareCell n (centralSeat n) := by
  rw [centralSeat_eq_square_add]
  unfold SquareCell
  constructor <;> nlinarith

/-- Qₙ=n(n+1)+1 なので、三根の Gap の積 n(n+1) とは互いに素である。 -/
theorem centralSeat_coprime_gaps (n : ℕ) : Nat.Coprime (centralSeat n) (n * (n + 1)) := by
  have he : centralSeat n = n * (n + 1) + 1 := by unfold centralSeat; ring
  rw [he, Nat.coprime_self_add_left]
  exact Nat.coprime_one_left _

/-- 連続二数の積は偶数なので、中央席は常に奇数。 -/
theorem centralSeat_odd (n : ℕ) : Odd (centralSeat n) := by
  have he : centralSeat n = n * (n + 1) + 1 := by unfold centralSeat; ring
  rw [he]
  exact (Nat.even_mul_succ_self n).add_one

/-- 中央席の素因子は2ではない。素数性なしでも除数2は排除できる。 -/
theorem divisor_ne_two {q n : ℕ} (hd : q ∣ centralSeat n) : q ≠ 2 := by
  rintro rfl
  exact (centralSeat_odd n).not_two_dvd_nat hd

/-- 中央席の素因子は三根の Gap n,n+1 のどちらも割らない。 -/
theorem prime_not_dvd_coordinates {q n : ℕ} (hq : q.Prime) (hd : q ∣ centralSeat n) :
    ¬ q ∣ n ∧ ¬ q ∣ n + 1 := by
  have hgap : ¬ q ∣ n * (n + 1) := by
    intro hg
    exact (Nat.not_coprime_of_dvd_of_dvd hq.one_lt hd hg) (centralSeat_coprime_gaps n)
  exact ⟨fun hn => hgap (dvd_mul_of_dvd_left hn _),
    fun hn => hgap (dvd_mul_of_dvd_right hn _)⟩

/-- 既存の中央席の素因子支持と一致する。旧素数の上界 q≤n も保存する。 -/
theorem mem_primeSupport_iff {q n : ℕ} :
    q ∈ squareOffsetPrimeSupport n (n + 1) ↔
      q.Prime ∧ q ≤ n ∧ q ∣ centralSeat n := by
  rw [mem_squareOffsetPrimeSupport, centralSeat_eq_square_add]

/-- 全ての n について作れる、本当の整係数 Weierstrass モデル Eₙ。 -/
def curve (n : ℕ) : WeierstrassCurve ℤ := FreyGapCubic.naive (n : ℤ) 1

/-- 有理数上の正規化モデル。整数モデルであるとは仮定しない。 -/
def rationalCurve (n : ℕ) : WeierstrassCurve ℚ := FreyGapCubic.normalized (n : ℚ) 1

/-- ℚへ写した同じ整数曲線から、許容座標変換で Wₙ を得る。
二つの c₄ の表示が、別々の曲線の偶然の一致ではないことを固定する。 -/
theorem rationalCurve_eq_change (n : ℕ) :
    rationalCurve n = FreyGapCubic.normalizeChange •
      (curve n).map (Int.castRingHom ℚ) := by
  rw [rationalCurve, FreyGapCubic.normalized_eq_change]
  congr 1
  ext <;> simp [curve, FreyGapCubic.naive, WeierstrassCurve.map]

/-- n>0 の時には有理数上の曲線も非特異。n=0 の零 Gap は除外する。 -/
theorem rationalCurve_isElliptic {n : ℕ} (hn : 0 < n) : (rationalCurve n).IsElliptic := by
  apply FreyGapCubic.normalized_isElliptic
  · exact_mod_cast hn.ne'
  · norm_num
  · have hnQ : (0 : ℚ) < n := by exact_mod_cast hn
    positivity

/-- 整数モデルの c₄ には16が掛かる。 -/
theorem curve_c4 (n : ℕ) : (curve n).c₄ = 16 * (centralSeat n : ℤ) := by
  rw [curve, FreyGapCubic.naive_c4]
  simp [centralSeat]

/-- 正規化された有理数モデルの c₄ が中央席そのもの。 -/
theorem rationalCurve_c4 (n : ℕ) : (rationalCurve n).c₄ = (centralSeat n : ℚ) := by
  rw [rationalCurve, FreyGapCubic.normalized_c4]
  simp [centralSeat]

/-- 整数モデルの判別式。素因子の支持を三つの Gap から読める形にする。 -/
theorem curve_discriminant (n : ℕ) : (curve n).Δ = 16 * (n : ℤ) ^ 2 * ((n : ℤ) + 1) ^ 2 := by
  rw [curve, FreyGapCubic.naive_discriminant]
  ring

/-- ℚ上での正規化には256の分母が現れる。 -/
theorem rationalCurve_discriminant (n : ℕ) :
    (rationalCurve n).Δ = ((n : ℚ) * ((n : ℚ) + 1)) ^ 2 / 256 := by
  rw [rationalCurve, FreyGapCubic.normalized_discriminant, mul_one]

/-- B=1 の正規化モデルを既存の整数モデルへ降ろせる条件は16∣n。
任意の n に対して c₄=Qₙ の整係数モデルを得たと誤解しないための境界。 -/
theorem integralNormalization_iff (n : ℕ) :
    FreyGapCubic.IntegralNormalization (n : ℤ) 1 ↔ (16 : ℤ) ∣ (n : ℤ) := by
  constructor
  · intro h
    simpa only [mul_one] using h.sixteen
  · intro h
    refine ⟨?_, by simpa only [mul_one] using h⟩
    have hf : (4 : ℤ) ∣ (n : ℤ) := dvd_trans (by norm_num : (4 : ℤ) ∣ 16) h
    convert dvd_neg.mpr hf using 1
    ring

/-- 分母条件が成立する場合には、c₄=Qₙ を整数モデルにも降ろせる。 -/
theorem integral_c4 (n : ℕ) (hn : (16 : ℤ) ∣ (n : ℤ)) :
    (FreyGapCubic.integral (n : ℤ) 1).c₄ = (centralSeat n : ℤ) := by
  rw [FreyGapCubic.integral_c4 _ _ ((integralNormalization_iff n).mpr hn)]
  simp [centralSeat]

/-- q∣Qₙ なら q∤Δ(Eₙ)。Qₙ の奇数性から q≠2 も内部で供給する。 -/
theorem prime_not_dvd_discriminant {q n : ℕ} (hq : q.Prime) (hd : q ∣ centralSeat n) :
    ¬ (q : ℤ) ∣ (curve n).Δ := by
  have hD : (curve n).Δ = ((16 * (n * (n + 1)) ^ 2 : ℕ) : ℤ) := by
    rw [curve_discriminant]
    push_cast
    ring
  rw [hD, Int.natCast_dvd_natCast]
  intro h
  rcases hq.dvd_mul.mp h with h16 | hgap
  · have h2 : q ∣ 2 := hq.dvd_of_dvd_pow (n := 4) (by simpa using h16)
    exact divisor_ne_two hd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2)
  · have hprod := hq.dvd_of_dvd_pow hgap
    rcases hq.dvd_mul.mp hprod with hn | hn
    · exact (prime_not_dvd_coordinates hq hd).1 hn
    · exact (prime_not_dvd_coordinates hq hd).2 hn

/-- 中央席の素因子は整数曲線の c₄ を割る一方、判別式は割らない。 -/
theorem prime_dvd_c4 {q n : ℕ} (hd : q ∣ centralSeat n) : (q : ℤ) ∣ (curve n).c₄ := by
  rw [curve_c4]
  exact dvd_mul_of_dvd_right (by exact_mod_cast hd) _

/-- 素因子 q ごとに実際の剰余体へモデルを写すと、非特異な楕円曲線になる。 -/
theorem reduction_isElliptic {q n : ℕ} (hq : q.Prime) (hd : q ∣ centralSeat n) :
    ((curve n).map (Int.castRingHom (ZMod q))).IsElliptic := by
  let : Fact q.Prime := ⟨hq⟩
  constructor
  rw [isUnit_iff_ne_zero, WeierstrassCurve.map_Δ]
  change ((curve n).Δ : ZMod q) ≠ 0
  intro hz
  exact prime_not_dvd_discriminant hq hd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz)

/-- 同じ剰余体モデルでは c₄=0。この零は曲線の特異性を意味しない。 -/
theorem reduction_c4_eq_zero {q n : ℕ} (hd : q ∣ centralSeat n) :
    ((curve n).map (Int.castRingHom (ZMod q))).c₄ = 0 := by
  rw [WeierstrassCurve.map_c₄]
  change ((curve n).c₄ : ZMod q) = 0
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (prime_dvd_c4 hd)

/-- q≠3 の素因子では n mod q の位数が正確に3。
(n−1)(n²+n+1)=n³−1 が冪等式を与え、n=1 は q∣3 を強制するため排除される。 -/
theorem orderOf_eq_three {q n : ℕ} (hq : q.Prime) (hq3 : q ≠ 3)
    (hd : q ∣ centralSeat n) : orderOf (n : ZMod q) = 3 := by
  let : Fact q.Prime := ⟨hq⟩
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hQ : (n : ZMod q) ^ 2 + (n : ZMod q) + 1 = 0 := by
    have h := (ZMod.natCast_eq_zero_iff (centralSeat n) q).mpr hd
    simpa only [centralSeat, Nat.cast_add, Nat.cast_pow, Nat.cast_one] using h
  apply orderOf_eq_prime
  · linear_combination ((n : ZMod q) - 1) * hQ
  · intro hn
    have h3 : (3 : ZMod q) = 0 := by
      calc
        (3 : ZMod q) = (n : ZMod q) ^ 2 + (n : ZMod q) + 1 := by rw [hn]; ring
        _ = 0 := hQ
    have hd3 : q ∣ 3 := (ZMod.natCast_eq_zero_iff 3 q).mp h3
    exact hq3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hd3)

/-- 非例外の素因子は1 mod 3。素因子の存在や中央席の素数性は結論しない。 -/
theorem prime_mod_three {q n : ℕ} (hq : q.Prime) (hq3 : q ≠ 3)
    (hd : q ∣ centralSeat n) : q % 3 = 1 := by
  let : Fact q.Prime := ⟨hq⟩
  have hn : (n : ZMod q) ≠ 0 := by
    intro hz
    exact (prime_not_dvd_coordinates hq hd).1 ((ZMod.natCast_eq_zero_iff n q).mp hz)
  have ho := orderOf_eq_three hq hq3 hd
  have hdiv : 3 ∣ q - 1 := by simpa only [ho] using ZMod.orderOf_dvd_card_sub_one hn
  have hmod := Nat.mod_eq_zero_of_dvd hdiv
  have hqpos := hq.two_le
  omega

/-- 例外素数3も含めた完全な「与えられた素因子」の分類。 -/
theorem prime_three_or_mod_three {q n : ℕ} (hq : q.Prime) (hd : q ∣ centralSeat n) :
    q = 3 ∨ q % 3 = 1 := by
  by_cases h3 : q = 3
  · exact Or.inl h3
  · exact Or.inr (prime_mod_three hq h3 hd)

/-- NOTE-006 の q>3 という前提で書いた合同式版。 -/
theorem prime_modEq_one {q n : ℕ} (hq : q.Prime) (hq3 : 3 < q) (hd : q ∣ centralSeat n) :
    q ≡ 1 [MOD 3] := by
  simpa only [Nat.ModEq, Nat.one_mod] using prime_mod_three hq (by omega) hd

/-- §3 の接続をまとめた入口。素因子が与えられた時の不変量・支持・合同類を返す。
ここから中央席そのものの素数性を推論することはできない。 -/
theorem prime_bridge {q n : ℕ} (hq : q.Prime) (hd : q ∣ centralSeat n) :
    (q : ℤ) ∣ (curve n).c₄ ∧ ¬ (q : ℤ) ∣ (curve n).Δ ∧
      (q = 3 ∨ q % 3 = 1) :=
  ⟨prime_dvd_c4 hd, prime_not_dvd_discriminant hq hd, prime_three_or_mod_three hq hd⟩

/-- 実際の平方殻の旧支持から使う入口。上界を落として素因子全体と混同しない。 -/
theorem prime_bridge_of_mem_support {q n : ℕ}
    (h : q ∈ squareOffsetPrimeSupport n (n + 1)) :
    q ≤ n ∧ (q : ℤ) ∣ (curve n).c₄ ∧ ¬ (q : ℤ) ∣ (curve n).Δ ∧
      (q = 3 ∨ q % 3 = 1) := by
  have hs := mem_primeSupport_iff.mp h
  exact ⟨hs.2.1, prime_bridge hs.1 hs.2.2⟩

end DkMath.NumberTheory.Legendre.FreyC4CentralSeat
