/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTwo

#print "file: DkMath.FLT.FreyPrimeProfile"

/-!
# NOTE-008: 最小判別式で素数2だけが残す剰余

同じ source・同じ最小モデルで、奇素数の付値は指数 p の倍数となり、2では −8 が残る。
p≥5 の素数なら −8≠0 mod p なので、p∣vℓ(Δ_min) と ℓ≠2 は同値となる。
これは局所付値の完全な算術的分類である。Artin 導手・残余表現の導手や
レベル降下による素数の除去を、この合同式の定義として導入しない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory FreyLocalReduction
variable {p : ℕ} (S : Source p)

/-- 分母256の2進補正を、指数pの剰余体へ直接輸送する。 -/
theorem two_discriminant_cast [Fact p.Prime] :
    (padicValRat 2 S.rationalCurve.Δ : ZMod p) = -8 := by
  rw [S.minimal_discriminant_valuation_two.2]
  push_cast
  simp

/-- 全素数の最小判別式付値を同一の剰余公式で記録する。ℓ=p の算術式も含む。 -/
theorem discriminant_cast_profile [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime] :
    (padicValRat ℓ S.rationalCurve.Δ : ZMod p) = if ℓ = 2 then -8 else 0 := by
  by_cases hℓ : ℓ = 2
  · subst ℓ
    simpa using S.two_discriminant_cast
  · rw [ite_eq_right hℓ, (S.minimal_discriminant_valuation (Fact.out : p.Prime).pos hℓ).2]
    push_cast
    simp

/-- p≥5 の素数は8を割らない。2を例外とする分類の指数側の根拠である。 -/
theorem prime_not_dvd_eight [Fact p.Prime] (hp : 5 ≤ p) : ¬ (p : ℤ) ∣ 8 := by
  have h2 : ¬ (p : ℤ) ∣ 2 := by
    intro hd
    have hdNat : p ∣ 2 := by exact_mod_cast hd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdNat with h1 | h2
    · omega
    · omega
  intro h8
  apply h2
  apply (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).dvd_of_dvd_pow (n := 3)
  simpa using h8

/-- 素数指数p≥5では、2の最小判別式付値は p の倍数ではない。 -/
theorem not_exponent_dvd_two_valuation [Fact p.Prime] (hp : 5 ≤ p) :
    ¬ (p : ℤ) ∣ padicValRat 2 S.rationalCurve.Δ :=
  fun hd => prime_not_dvd_eight hp (S.exponent_dvd_two_valuation_iff.mp hd)

/-- 素数全体で p倍性を持つ場所を正確に分類する。導手の構成とは独立の保存則。 -/
theorem exponent_dvd_valuation_iff_ne_two [Fact p.Prime] (hp : 5 ≤ p)
    {ℓ : ℕ} [Fact ℓ.Prime] :
    (p : ℤ) ∣ padicValRat ℓ S.rationalCurve.Δ ↔ ℓ ≠ 2 := by
  by_cases hℓ : ℓ = 2
  · subst ℓ
    exact iff_of_false (S.not_exponent_dvd_two_valuation hp) (by simp)
  · exact iff_of_true (S.minimal_discriminant_exponent_dvd (by omega) hℓ).2 hℓ

end DkMath.FLT.Frey.Source
