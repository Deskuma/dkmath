/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Frey
import DkMath.Lib.NumberTheory.FreyTwoArithmetic

#print "file: DkMath.FLT.FreyTwo"

/-!
# NOTE-007: 素数2の正規化モデル

整数モデルの分母条件 4∣B−A−1 は A,B の異なる偶奇を強制し、c₄=A²+AB+B² は奇数。
従って既存の一般 DVR 定理で2でも同じモデルが最小になる。判別式の付値では
分母256の補正 −8 を消さず、v₂(Δ_min)=2p v₂(abc)−8 として保持する。
p≥5 なら v₂(abc)≥1 から乗法的還元となる。任意の原始反例の向き付け、
Artin 導手・ガロア表現・レベル降下は、ここで得る還元型とは別の境界である。
-/

namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory FreyGapCubic FreyPrimeValuation FreyLocalReduction
variable {p : ℕ} (S : Source p)
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- 同じ有理モデルは2でも最小。素数ごとに別の整モデルを選ばない。 -/
theorem isMinimal_at_two : WeierstrassCurve.IsMinimal (LocalRing 2) S.rationalCurve := by
  rw [← S.curve_map]
  exact isMinimal_at_prime_of_not_dvd_c4 2 S.curve
    (not_two_dvd_integral_c4 _ _ S.normalization)

/-- 整係数条件がある source の積 abc は必ず偶数である。 -/
theorem two_dvd_product : (2 : ℤ) ∣ S.a * S.b * S.c := by
  have hpow : (2 : ℤ) ∣ (S.a * S.b) ^ p := by
    rw [mul_pow]
    exact dvd_trans (by norm_num : (2 : ℤ) ∣ 16) S.normalization.sixteen
  exact dvd_mul_of_dvd_left (Int.prime_two.dvd_of_dvd_pow hpow) S.c

/-- 非零積の2進付値は1以上。零に対する付値のデフォルト値を使わない。 -/
theorem one_le_product_two_valuation : 1 ≤ padicValInt 2 (S.a * S.b * S.c) := by
  have hne : padicValInt 2 (S.a * S.b * S.c) ≠ 0 := by
    intro hz
    rcases padicValInt.eq_zero_iff.mp hz with h | h | h
    · exact (by decide : (2 : ℕ) ≠ 1) h
    · exact S.product_ne_zero h
    · exact h S.two_dvd_product
  omega

/-- 最小判別式の2進付値は −8 の補正を含む整数等式である。 -/
theorem minimal_discriminant_valuation_two :
    WeierstrassCurve.IsMinimal (LocalRing 2) S.rationalCurve ∧
      padicValRat 2 S.rationalCurve.Δ =
        (2 * p : ℕ) * (padicValInt 2 (S.a * S.b * S.c) : ℤ) - 8 := by
  refine ⟨S.isMinimal_at_two, ?_⟩
  simpa only [Source.rationalCurve, padicValNat.self (by decide : 1 < 2),
    Int.natCast_one, mul_one] using
    valuation_of_solution (ℓ := 2) S.equation S.product_ne_zero

/-- 2では p倍性の障害は正確に8。奇素数の p∣vℓ(Δ) を2へ延長しない。 -/
theorem exponent_dvd_two_valuation_iff :
    (p : ℤ) ∣ padicValRat 2 S.rationalCurve.Δ ↔ (p : ℤ) ∣ 8 := by
  rw [S.minimal_discriminant_valuation_two.2]
  have hm : (p : ℤ) ∣ (2 * p : ℕ) * (padicValInt 2 (S.a * S.b * S.c) : ℤ) :=
    ⟨2 * (padicValInt 2 (S.a * S.b * S.c) : ℤ), by push_cast; ring⟩
  constructor
  · intro h
    convert dvd_sub hm h using 1
    ring
  · exact dvd_sub hm

/-- 任意の source は2で良還元または乗法的還元。整係数モデルの c₄ は常に単元。 -/
theorem good_or_multiplicative_at_two :
    WeierstrassCurve.HasGoodReduction (LocalRing 2) S.rationalCurve ∨
      WeierstrassCurve.HasMultiplicativeReduction (LocalRing 2) S.rationalCurve := by
  rw [← S.curve_map]
  by_cases hd : (2 : ℤ) ∣ S.curve.Δ
  · exact Or.inr (hasMultiplicativeReduction_at_prime 2 S.curve hd
      (not_two_dvd_integral_c4 _ _ S.normalization))
  · exact Or.inl (hasGoodReduction_at_prime 2 S.curve hd)

/-- p≥5 では v₂(Δ_min)≥2 なので、2は乗法的還元の素数になる。 -/
theorem hasMultiplicativeReduction_at_two (hp : 5 ≤ p) :
    WeierstrassCurve.HasMultiplicativeReduction (LocalRing 2) S.rationalCurve := by
  have hv : 0 < padicValRat 2 S.rationalCurve.Δ := by
    rw [S.minimal_discriminant_valuation_two.2]
    have hV := S.one_le_product_two_valuation
    have hpZ : (5 : ℤ) ≤ p := by exact_mod_cast hp
    have hVZ : (1 : ℤ) ≤ padicValInt 2 (S.a * S.b * S.c) := by exact_mod_cast hV
    push_cast
    nlinarith
  have hval : (padicValInt 2 S.curve.Δ : ℤ) = padicValRat 2 S.rationalCurve.Δ := by
    have hΔ := congrArg WeierstrassCurve.Δ S.curve_map
    rw [WeierstrassCurve.map_Δ] at hΔ
    change (S.curve.Δ : ℚ) = S.rationalCurve.Δ at hΔ
    rw [← hΔ, padicValRat.of_int]
  have hd : (2 : ℤ) ∣ S.curve.Δ := by
    by_contra hnot
    rw [padicValInt.eq_zero_of_not_dvd hnot, Int.natCast_zero] at hval
    linarith
  rw [← S.curve_map]
  exact hasMultiplicativeReduction_at_prime 2 S.curve hd
    (not_two_dvd_integral_c4 _ _ S.normalization)

/-- NOTE-006 の奇素数定理と2の定理を合成した、全素数での最小性。 -/
theorem isMinimal_every_prime (hp : 0 < p) {ℓ : ℕ} [Fact ℓ.Prime] :
    WeierstrassCurve.IsMinimal (LocalRing ℓ) S.rationalCurve := by
  by_cases hℓ : ℓ = 2
  · subst ℓ; exact S.isMinimal_at_two
  · exact S.isMinimal_at_odd_prime hp hℓ

/-- 全素数での半安定性。整数モデルの向き付け済み前提は Source に保持される。 -/
theorem good_or_multiplicative_every_prime (hp : 0 < p) {ℓ : ℕ} [Fact ℓ.Prime] :
    WeierstrassCurve.HasGoodReduction (LocalRing ℓ) S.rationalCurve ∨
      WeierstrassCurve.HasMultiplicativeReduction (LocalRing ℓ) S.rationalCurve := by
  by_cases hℓ : ℓ = 2
  · subst ℓ; exact S.good_or_multiplicative_at_two
  · exact S.good_or_multiplicative hp hℓ

/-- p≥5 では乗法的還元の全素数支持が abc の素因子支持と一致する。
これは還元型の支持であり、Artin 導手の構成を代用する定義ではない。 -/
theorem multiplicative_support_iff (hp : 5 ≤ p) {ℓ : ℕ} [Fact ℓ.Prime] :
    WeierstrassCurve.HasMultiplicativeReduction (LocalRing ℓ) S.rationalCurve ↔
      (ℓ : ℤ) ∣ S.a * S.b * S.c := by
  by_cases hℓ : ℓ = 2
  · subst ℓ
    exact iff_of_true (S.hasMultiplicativeReduction_at_two hp) S.two_dvd_product
  · exact S.hasMultiplicativeReduction_iff (by omega) hℓ

end DkMath.FLT.Frey.Source
