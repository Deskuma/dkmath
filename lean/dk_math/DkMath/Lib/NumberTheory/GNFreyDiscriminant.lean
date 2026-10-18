/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.FreyGapCubic
import DkMath.Lib.Cosmic.CoreNested
import DkMath.CosmicFormula.Defs

#print "file: DkMath.Lib.NumberTheory.GNFreyDiscriminant"

/-!
# NOTE-005: GN → 三根の Gap → Frey 判別式

奇数冪の和は `(a+b) GN_p(a+b,−b)` である。この恒等式には FLT の方程式も
正則性も不要で、a+b=0 でも成立する。これを実際の曲線の Δ に代入する。
FLT 方程式を追加した場合に限り、三つの Gap の積を (abc)^p に書き換える。

正規化の分母条件は別途証明する。a≡−1 (mod 4)、b が偶数、p≥4 が十分であり、
奇数性は a^p≡−1 (mod 4) に使う。反例をこの向きへ置換する処理や、最小モデル・
Galois 表現・モジュラー性への移行は、この代数恒等式に含まれない。
-/

namespace DkMath.Lib.NumberTheory.GNFreyDiscriminant

open FreyGapCubic

/-- 同じ Gap を保持した GN 因子。記号の別名であり新しい除算を導入しない。 -/
def gnFactor {R : Type*} [CommRing R] (p : ℕ) (a b : R) : R :=
  DkMath.CosmicFormula.GN p (a + b) (-b)

/-- 奇数冪和の GN 表示。零の Gap を打ち消さず、全ての入力で成立する。 -/
theorem sum_eq_gap_gn {R : Type*} [CommRing R] {p : ℕ} (hp : Odd p) (a b : R) :
    a ^ p + b ^ p = (a + b) * gnFactor p a b :=
  DkMath.Lib.Cosmic.odd_sum_eq_mul_gtail_one hp a b

private theorem power_pair_square {R : Type*} [CommRing R] (a b : R) (p : ℕ) :
    (a ^ p * b ^ p) ^ 2 = (a * b) ^ (2 * p) := by
  rw [← mul_pow, ← pow_mul, Nat.mul_comm p 2]

/-- 素朴なモデルの16を保持した、全ての可換環上の GN 判別式。 -/
theorem naive_discriminant_gn {R : Type*} [CommRing R] {p : ℕ} (hp : Odd p) (a b : R) :
    (naive (a ^ p) (b ^ p)).Δ =
      16 * ((a * b) ^ (2 * p) * ((a + b) * gnFactor p a b) ^ 2) := by
  rw [naive_discriminant, sum_eq_gap_gn hp, mul_pow, power_pair_square]

/-- 正規化モデルの Δ を GN で厳密に表示する。ここでは整係数性を主張しない。 -/
theorem normalized_discriminant_gn {p : ℕ} (hp : Odd p) (a b : ℚ) :
    (normalized (a ^ p) (b ^ p)).Δ =
      (a * b) ^ (2 * p) * ((a + b) * gnFactor p a b) ^ 2 / 256 := by
  rw [normalized_discriminant, sum_eq_gap_gn hp, mul_pow, power_pair_square]

/-- FLT 方程式を入力にした時だけ、三根の差の積の平方が (abc)^(2p) になる。 -/
theorem gap_product_of_solution {R : Type*} [CommRing R] {p : ℕ} {a b c : R}
    (heq : a ^ p + b ^ p = c ^ p) :
    (a ^ p * b ^ p * (a ^ p + b ^ p)) ^ 2 = (a * b * c) ^ (2 * p) := by
  have hprod : a ^ p * b ^ p * (a ^ p + b ^ p) = (a * b * c) ^ p := by
    rw [heq, mul_pow, mul_pow]
  rw [hprod, ← pow_mul, Nat.mul_comm p 2]

/-- 実際の正規化曲線の Δ=2⁻⁸(abc)^(2p)。非零性を要しない恒等式。 -/
theorem normalized_discriminant_of_solution {p : ℕ} {a b c : ℚ}
    (heq : a ^ p + b ^ p = c ^ p) :
    (normalized (a ^ p) (b ^ p)).Δ = (a * b * c) ^ (2 * p) / 256 := by
  rw [normalized_discriminant, gap_product_of_solution heq]

/-- c₄=c^(2p)−(ab)^p。方程式を使う箇所はこの等式の前提として明示する。 -/
theorem normalized_c4_of_solution {p : ℕ} {a b c : ℚ}
    (heq : a ^ p + b ^ p = c ^ p) :
    (normalized (a ^ p) (b ^ p)).c₄ = c ^ (2 * p) - (a * b) ^ p := by
  have hc : c ^ (2 * p) = (c ^ p) ^ 2 := by rw [← pow_mul, Nat.mul_comm p 2]
  rw [normalized_c4, hc, ← heq, mul_pow]
  ring

/-- 標準的な向き付け条件から、整数モデルの分母条件を実際に供給する。
`4 ∣ a+1` は a≡3 (mod 4) の符号を曖昧にしない表現である。 -/
theorem normalization_of_oriented {p : ℕ} (hp : Odd p) (hp4 : 4 ≤ p)
    {a b : ℤ} (ha : 4 ∣ a + 1) (hb : Even b) :
    IntegralNormalization (a ^ p) (b ^ p) := by
  have hb2 : (2 : ℤ) ∣ b := even_iff_two_dvd.mp hb
  have hb16 : (16 : ℤ) ∣ b ^ p := by
    simpa using (pow_dvd_pow_of_dvd_of_le hb2 hp4 : (2 : ℤ) ^ 4 ∣ b ^ p)
  have ha4 : (a : ZMod 4) = -1 := by
    have hz : ((a + 1 : ℤ) : ZMod 4) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ha
    push_cast at hz
    linear_combination hz
  have hap : (4 : ℤ) ∣ a ^ p + 1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (a ^ p + 1) 4).mp
    push_cast
    rw [ha4, hp.neg_one_pow]
    ring
  refine ⟨?_, dvd_mul_of_dvd_right hb16 _⟩
  have hb4 : (4 : ℤ) ∣ b ^ p := dvd_trans (by norm_num : (4 : ℤ) ∣ 16) hb16
  convert dvd_sub hb4 hap using 1
  ring

/-- 整係数モデルでも、GN による判別式の保存則を分母なしで保持できる。 -/
theorem integral_discriminant_gn {p : ℕ} (hp : Odd p) (a b : ℤ)
    (hn : IntegralNormalization (a ^ p) (b ^ p)) :
    256 * (integral (a ^ p) (b ^ p)).Δ =
      (a * b) ^ (2 * p) * ((a + b) * gnFactor p a b) ^ 2 := by
  rw [integral_discriminant _ _ hn, sum_eq_gap_gn hp, mul_pow, power_pair_square]

/-- 整数方程式から得る分母を払った保存則。零入力も許す代数等式である。 -/
theorem integral_discriminant_of_solution {p : ℕ} {a b c : ℤ}
    (hn : IntegralNormalization (a ^ p) (b ^ p)) (heq : a ^ p + b ^ p = c ^ p) :
    256 * (integral (a ^ p) (b ^ p)).Δ = (a * b * c) ^ (2 * p) := by
  rw [integral_discriminant _ _ hn, gap_product_of_solution heq]

end DkMath.Lib.NumberTheory.GNFreyDiscriminant
