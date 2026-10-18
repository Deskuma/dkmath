/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.GNFreyDiscriminant
import DkMath.Lib.NumberTheory.PadicValNat

#print "file: DkMath.Lib.NumberTheory.FreyPrimeValuation"

/-!
# NOTE-005: GN 判別式の局所付値と原始性

有理数の付値には整数値の `padicValRat` を使う。分母256は奇素数では消えるが、
素数2では8を引く。この補正を先に一般式として証明し、奇素数で特殊化する。
Mathlib の付値は0に対して0を返すので、積の付値を計算する定理では非零条件を残す。

原始性から、AB(A+B) の素因子は A²+AB+B² を割れないことを別途証明する。
これにより「判別式の付値が p の倍数」と「同じ素数が c₄ を割らない」を得る。
この二つは局所算術の入力であり、最小性・還元型・導手・Galois 表現の性質を
このファイルで定義したことにはならない。特に ℓ=p にも算術式は成立するが、
レベル降下で ℓ=p を扱うための追加理論を省略できるという意味ではない。
-/

namespace DkMath.Lib.NumberTheory.FreyPrimeValuation

open FreyGapCubic GNFreyDiscriminant

/-- 原始な二つの元とその和の素因子は c₄ 型の二次式を割らない。
素数2も含む純粋な整数可除性の定理であり、楕円曲線の理論を使わない。 -/
theorem prime_not_dvd_c4_form {q A B : ℤ} (hq : Prime q) (hab : IsCoprime A B)
    (hd : q ∣ A * B * (A + B)) : ¬ q ∣ A ^ 2 + A * B + B ^ 2 := by
  intro hD
  have fromA (hA : q ∣ A) : False := by
    have hb2 : q ∣ B ^ 2 := by
      convert dvd_sub hD (dvd_mul_of_dvd_left hA (A + B)) using 1
      ring
    exact hq.not_isUnit (hab.isUnit_of_dvd' hA (hq.dvd_of_dvd_pow hb2))
  have fromB (hB : q ∣ B) : False := by
    have ha2 : q ∣ A ^ 2 := by
      convert dvd_sub hD (dvd_mul_of_dvd_left hB (A + B)) using 1
      ring
    exact hq.not_isUnit (hab.isUnit_of_dvd' (hq.dvd_of_dvd_pow ha2) hB)
  rcases hq.dvd_mul.mp hd with hAB | hS
  · exact (hq.dvd_mul.mp hAB).elim fromA fromB
  · have hAB : q ∣ A * B := by
      have hs2 : q ∣ (A + B) ^ 2 := dvd_pow hS (by decide)
      convert dvd_sub hs2 hD using 1
      ring
    exact (hq.dvd_mul.mp hAB).elim fromA fromB

/-- 原始的な整数冪和解の積 abc の素因子は、実際の整数曲線の c₄ を割らない。 -/
theorem not_dvd_integral_c4 {p ℓ : ℕ} (hp : 0 < p) (hℓ : ℓ.Prime)
    {a b c : ℤ} (hab : IsCoprime a b) (heq : a ^ p + b ^ p = c ^ p)
    (hn : IntegralNormalization (a ^ p) (b ^ p)) (hd : (ℓ : ℤ) ∣ a * b * c) :
    ¬ (ℓ : ℤ) ∣ (integral (a ^ p) (b ^ p)).c₄ := by
  rw [integral_c4 _ _ hn]
  apply prime_not_dvd_c4_form (Nat.prime_iff_prime_int.mp hℓ) (hab.pow (m := p) (n := p))
  have hprod : a ^ p * b ^ p * (a ^ p + b ^ p) = (a * b * c) ^ p := by
    rw [heq, mul_pow, mul_pow]
  rw [hprod]
  exact dvd_pow hd hp.ne'

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- 分母256の補正を含む基本式。素数2を奇素数と混ぜない。 -/
theorem valuation_scaled_power (p : ℕ) (z : ℤ) (hz : z ≠ 0) :
    padicValRat ℓ (((z : ℚ) ^ (2 * p)) / 256) =
      (2 * p : ℕ) * (padicValInt ℓ z : ℤ) - 8 * (padicValNat ℓ 2 : ℤ) := by
  have hzQ : (z : ℚ) ≠ 0 := by exact_mod_cast hz
  rw [show (256 : ℚ) = 2 ^ 8 by norm_num,
    padicValRat.div (pow_ne_zero _ hzQ) (by norm_num), padicValRat.pow, padicValRat.pow]
  rw [padicValRat.of_int,
    show padicValRat ℓ (2 : ℚ) = (padicValNat ℓ 2 : ℤ) from padicValRat.of_nat]
  norm_num

/-- 奇素数では2の付値は0。分母の寄与を消すための条件を明示する。 -/
theorem valuation_two_eq_zero (hℓ2 : ℓ ≠ 2) : padicValNat ℓ 2 = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  intro hd
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
  · exact (Fact.out : ℓ.Prime).ne_one h1
  · exact hℓ2 h2

/-- FLT 方程式の非零積から、実際の有理数モデルの判別式付値へ輸送する。
素数2の補正項を含むため、奇素数専用の式との境界が見える。 -/
theorem valuation_of_solution {p : ℕ} {a b c : ℤ}
    (heq : a ^ p + b ^ p = c ^ p) (habc : a * b * c ≠ 0) :
    padicValRat ℓ (normalized ((a : ℚ) ^ p) ((b : ℚ) ^ p)).Δ =
      (2 * p : ℕ) * (padicValInt ℓ (a * b * c) : ℤ) - 8 * (padicValNat ℓ 2 : ℤ) := by
  have hQ : (a : ℚ) ^ p + (b : ℚ) ^ p = (c : ℚ) ^ p := by exact_mod_cast heq
  rw [normalized_discriminant_of_solution hQ]
  simpa only [Int.cast_mul] using valuation_scaled_power (ℓ := ℓ) p (a * b * c) habc

/-- 奇素数での保存則 vℓ(Δ_norm)=2p vℓ(abc)。ℓ∣abc すら不要な等式である。 -/
theorem valuation_of_solution_odd {p : ℕ} (hℓ2 : ℓ ≠ 2) {a b c : ℤ}
    (heq : a ^ p + b ^ p = c ^ p) (habc : a * b * c ≠ 0) :
    padicValRat ℓ (normalized ((a : ℚ) ^ p) ((b : ℚ) ^ p)).Δ =
      (2 * p : ℕ) * (padicValInt ℓ (a * b * c) : ℤ) := by
  rw [valuation_of_solution heq habc, valuation_two_eq_zero hℓ2]
  simp

/-- 整係数性を追加すれば自然数値の整数付値でも同じ保存則が得られる。 -/
theorem integral_valuation_of_solution {p : ℕ} (hℓ2 : ℓ ≠ 2) {a b c : ℤ}
    (hn : IntegralNormalization (a ^ p) (b ^ p))
    (heq : a ^ p + b ^ p = c ^ p) (habc : a * b * c ≠ 0) :
    padicValInt ℓ (integral (a ^ p) (b ^ p)).Δ = 2 * p * padicValInt ℓ (a * b * c) := by
  have hmap := congrArg WeierstrassCurve.Δ (integral_map (a ^ p) (b ^ p) hn)
  rw [WeierstrassCurve.map_Δ] at hmap
  change ((integral (a ^ p) (b ^ p)).Δ : ℚ) = _ at hmap
  have hΔ : ((integral (a ^ p) (b ^ p)).Δ : ℚ) =
      (normalized ((a : ℚ) ^ p) ((b : ℚ) ^ p)).Δ := by
    simpa only [Int.cast_pow] using hmap
  have hv := valuation_of_solution_odd hℓ2 heq habc
  rw [← hΔ, padicValRat.of_int] at hv
  exact_mod_cast hv

/-- 付値の p 倍性。これは Galois 表現の不分岐性の証明とは別の算術的結論。 -/
theorem exponent_dvd_integral_valuation {p : ℕ} (hℓ2 : ℓ ≠ 2) {a b c : ℤ}
    (hn : IntegralNormalization (a ^ p) (b ^ p))
    (heq : a ^ p + b ^ p = c ^ p) (habc : a * b * c ≠ 0) :
    p ∣ padicValInt ℓ (integral (a ^ p) (b ^ p)).Δ := by
  rw [integral_valuation_of_solution hℓ2 hn heq habc]
  exact ⟨2 * padicValInt ℓ (a * b * c), by ring⟩

/-- 奇素数での判別式の支持は abc の支持そのもの。
分母256を割る素数2を除き、整数等式と素元の可除性だけで証明する。 -/
theorem prime_dvd_integral_discriminant_iff {p : ℕ} (hp : 0 < p) (hℓ2 : ℓ ≠ 2)
    {a b c : ℤ} (hn : IntegralNormalization (a ^ p) (b ^ p))
    (heq : a ^ p + b ^ p = c ^ p) :
    (ℓ : ℤ) ∣ (integral (a ^ p) (b ^ p)).Δ ↔ (ℓ : ℤ) ∣ a * b * c := by
  have hq : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have h2 : ¬ (ℓ : ℤ) ∣ 2 := by
    intro hd
    have hn2 : ℓ ∣ 2 := by exact_mod_cast hd
    rcases (Nat.dvd_prime Nat.prime_two).mp hn2 with h1 | he
    · exact (Fact.out : ℓ.Prime).ne_one h1
    · exact hℓ2 he
  have h256 : ¬ (ℓ : ℤ) ∣ 256 := by
    intro hd
    apply h2
    apply hq.dvd_of_dvd_pow (n := 8)
    simpa using hd
  have hΔ := integral_discriminant_of_solution hn heq
  constructor
  · intro hd
    have hs := dvd_mul_of_dvd_right hd (256 : ℤ)
    rw [hΔ] at hs
    exact hq.dvd_of_dvd_pow hs
  · intro hd
    have hs := dvd_pow hd (Nat.mul_ne_zero (by decide : 2 ≠ 0) hp.ne')
    rw [← hΔ] at hs
    exact (hq.dvd_mul.mp hs).resolve_left h256

/-- GN の内部因子も付値の式に残す。非零の Gap と GN は非零の冪和から従う。
反例の右辺 c を導入しなくても、任意の奇数冪和に対して成立する。 -/
theorem valuation_gn {p : ℕ} (hp : Odd p) (hℓ2 : ℓ ≠ 2) (a b : ℚ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hs : a ^ p + b ^ p ≠ 0) :
    padicValRat ℓ (normalized (a ^ p) (b ^ p)).Δ =
      (2 * p : ℕ) * (padicValRat ℓ a + padicValRat ℓ b) +
        2 * (padicValRat ℓ (a + b) + padicValRat ℓ (gnFactor p a b)) := by
  have hfac : (a + b) * gnFactor p a b ≠ 0 := by rwa [← sum_eq_gap_gn hp]
  have hg := (mul_ne_zero_iff.mp hfac)
  rw [normalized_discriminant_gn hp,
    padicValRat.div (mul_ne_zero (pow_ne_zero _ (mul_ne_zero ha hb)) (pow_ne_zero _ hfac))
      (by norm_num), padicValRat.mul (pow_ne_zero _ (mul_ne_zero ha hb)) (pow_ne_zero _ hfac),
    padicValRat.pow, padicValRat.pow, padicValRat.mul ha hb, padicValRat.mul hg.1 hg.2]
  have h256 : padicValRat ℓ (256 : ℚ) = 0 := by
    rw [show (256 : ℚ) = 2 ^ 8 by norm_num, padicValRat.pow]
    rw [show padicValRat ℓ (2 : ℚ) = (padicValNat ℓ 2 : ℤ) from padicValRat.of_nat,
      valuation_two_eq_zero hℓ2]
    norm_num
  rw [h256, sub_zero]
  norm_num

end DkMath.Lib.NumberTheory.FreyPrimeValuation
